import asyncio
import inspect
import json
import os
import random
import time
import uuid
from collections import defaultdict, Counter

import aiohttp
from aiohttp import web
import requests
import websockets
from treys import Card, Evaluator, Deck

# =====================================================================
# 1. CONFIGURATION & ENVIRONMENT
# =====================================================================
API_KEY = os.getenv("OPEN_POKER_API_KEY", "sO03ApKecoElfE0-GfeMQC7GI4XJ-0qjX_2vGtXXbjQ")
WS_URL = os.getenv("OPEN_POKER_WS_URL", "wss://openpoker.ai/ws")
REST_BASE_URL = os.getenv("OPEN_POKER_REST_URL", "https://openpoker.ai")
PORT = int(os.getenv("PORT", 10000))
RENDER_EXTERNAL_URL = os.getenv("RENDER_EXTERNAL_URL", "")  # Auto-injected by Render

# Stop at 8k sims or 8s, whichever comes first
MC_TIME_BUDGET = float(os.getenv("MC_TIME_BUDGET", "8"))
MC_MAX_ITERS = int(os.getenv("MC_MAX_ITERS", "8000"))
BUY_IN_AMOUNT = int(os.getenv("BUY_IN_AMOUNT", "1500"))

FULL_DECK_INTS = Deck.GetFullDeck()

# =====================================================================
# 2. PREFLOP RANGE CHARTS & HAND SCORING
# =====================================================================
PREFLOP_TIER_1 = {  # Premium (~5%): 3-Bet / 4-Bet Value
    "AA", "KK", "QQ", "JJ", "TT", "AKs", "AQs", "AKo"
}
PREFLOP_TIER_2 = {  # Strong (~11%): Open UTG/MP, Call 3-Bets, 3-Bet IP
    "99", "88", "77", "AJs", "ATs", "KQs", "KJs", "QJs", "JTs", "AQo", "AJo", "KQo"
}
PREFLOP_TIER_3 = {  # Playable (~22%): Open CO, Defend BB, Call single raises IP
    "66", "55", "44", "33", "22",
    "A9s", "A8s", "A7s", "A6s", "A5s", "A4s", "A3s", "A2s",
    "KTs", "K9s", "QTs", "Q9s", "J9s", "T9s", "98s", "87s", "76s", "65s",
    "ATo", "KJo", "KTo", "QJo"
}
PREFLOP_TIER_4 = {  # Steal / Wide Defend (~38%): Open BTN/SB
    "K8s", "K7s", "K6s", "K5s", "Q8s", "J8s", "T8s", "97s", "86s", "75s", "54s",
    "A9o", "A8o", "A7o", "A5o", "K9o", "QTo", "JTo", "T9o", "98o"
}
THREE_BET_BLUFFS = {"A5s", "A4s", "A3s", "A2s", "K9s", "Q9s", "T8s", "98s", "87s", "76s"}
FOUR_BET_VALUE = {"AA", "KK", "QQ", "AKs"}

# Compact combo-class ranges (hand strings). Tiny RAM; used for MC sampling + decisions.
RANGE_TIER = {
    1: frozenset(PREFLOP_TIER_1),
    2: frozenset(PREFLOP_TIER_1 | PREFLOP_TIER_2),
    3: frozenset(PREFLOP_TIER_1 | PREFLOP_TIER_2 | PREFLOP_TIER_3),
    4: frozenset(PREFLOP_TIER_1 | PREFLOP_TIER_2 | PREFLOP_TIER_3 | PREFLOP_TIER_4),
}
RANGE_VS_3BET = frozenset(PREFLOP_TIER_1 | PREFLOP_TIER_2)

def cards_to_hand_str(c1: int, c2: int) -> str:
    r1, r2 = Card.get_rank_int(c1), Card.get_rank_int(c2)
    s1, s2 = Card.get_suit_int(c1), Card.get_suit_int(c2)
    chars = "23456789TJQKA"
    if r1 == r2:
        return f"{chars[r1]}{chars[r2]}"
    high, low = (r1, r2) if r1 > r2 else (r2, r1)
    suffix = "s" if s1 == s2 else "o"
    return f"{chars[high]}{chars[low]}{suffix}"

def hand_preflop_tier(hand_str: str) -> int:
    if hand_str in PREFLOP_TIER_1:
        return 1
    if hand_str in PREFLOP_TIER_2:
        return 2
    if hand_str in PREFLOP_TIER_3:
        return 3
    if hand_str in PREFLOP_TIER_4:
        return 4
    return 5


def classify_board(community_cards):
    """Cheap texture tags. No lookups beyond the 3–5 board cards."""
    info = {"paired": False, "flushy": False, "connected": False, "dry": True, "wet": False, "high": False}
    if len(community_cards) < 3:
        return info
    ranks = [Card.get_rank_int(c) for c in community_cards]
    suits = [Card.get_suit_int(c) for c in community_cards]
    flop_ranks = ranks[:3]
    info["paired"] = len(ranks) != len(set(ranks))
    suit_max = Counter(suits).most_common(1)[0][1]
    info["flushy"] = suit_max >= 3
    two_tone = suit_max == 2
    span = max(flop_ranks) - min(flop_ranks)
    info["connected"] = span <= 4 and len(set(flop_ranks)) >= 2
    info["high"] = max(ranks) >= 11
    info["wet"] = info["flushy"] or (info["connected"] and two_tone) or (info["connected"] and not info["paired"] and info["high"])
    info["dry"] = (not info["flushy"] and not info["connected"]) or (info["paired"] and not info["flushy"])
    return info


def classify_line(adj_equity: float) -> str:
    if adj_equity >= 0.66:
        return "value"
    if adj_equity >= 0.40:
        return "draw"
    return "air"


def empty_line_plan(hand_id=None):
    return {"hand_id": hand_id, "line": "none", "streets_bet": 0, "flop_checked": False}

# =====================================================================
# 3. LIVE OPPONENT TRACKER (HUD)
# =====================================================================
class OpponentTracker:
    """Tracks opponent VPIP, PFR, and post-flop aggression across the session."""
    def __init__(self):
        self.stats = defaultdict(lambda: {
            "hands": 0,
            "vpip": 0,
            "pfr": 0,
            "postflop_aggressive": 0,
            "postflop_passive": 0,
        })
        self.hand_vpip_flagged = set()
        self.hand_pfr_flagged = set()

    def start_new_hand(self, players):
        self.hand_vpip_flagged.clear()
        self.hand_pfr_flagged.clear()
        for p in players:
            pid = p.get("id") or p.get("name") or str(p.get("seat"))
            if pid:
                self.stats[pid]["hands"] += 1

    def record_action(self, pid: str, action: str, is_preflop: bool):
        if not pid:
            return
        s = self.stats[pid]
        if is_preflop:
            if action in ("call", "raise", "bet", "all_in") and pid not in self.hand_vpip_flagged:
                s["vpip"] += 1
                self.hand_vpip_flagged.add(pid)
            if action in ("raise", "bet", "all_in") and pid not in self.hand_pfr_flagged:
                s["pfr"] += 1
                self.hand_pfr_flagged.add(pid)
        else:
            if action in ("raise", "bet", "all_in"):
                s["postflop_aggressive"] += 1
            elif action in ("call", "check"):
                s["postflop_passive"] += 1

    def get_vpip(self, pid: str) -> float:
        s = self.stats.get(pid)
        if not s or s["hands"] < 5:
            return 0.32  # Default population VPIP assumption
        return max(0.10, min(0.85, s["vpip"] / s["hands"]))

    def get_aggression_factor(self, pid: str) -> float:
        s = self.stats.get(pid)
        if not s or (s["postflop_aggressive"] + s["postflop_passive"]) < 4:
            return 1.0
        return (s["postflop_aggressive"] + 1) / (s["postflop_passive"] + 1)


# =====================================================================
# 4. MONTE CARLO EQUITY & GTO/EXPLOITATIVE ENGINE
# =====================================================================
class ComprehensivePokerEngine:
    def __init__(self, tracker: OpponentTracker):
        self.evaluator = Evaluator()
        self.tracker = tracker

    def sample_opponent_hand(self, available_cards, allowed_hands):
        """Rejection-samples a hole pair from `allowed_hands` (combo-class strings)."""
        n = len(available_cards)
        if n < 2:
            return None
        last = None
        tries = 6 if allowed_hands is not None else 1
        for _ in range(tries):
            i = random.randrange(n)
            j = random.randrange(n - 1)
            if j >= i:
                j += 1
            last = [available_cards[i], available_cards[j]]
            if allowed_hands is None or cards_to_hand_str(last[0], last[1]) in allowed_hands:
                return last
        return last

    def estimate_equity(
        self,
        hole_cards,
        community_cards,
        num_opponents: int,
        opp_max_tier: int,
        time_budget: float = MC_TIME_BUDGET,
        allowed_hands=None,
    ):
        """
        Runs Monte Carlo until `time_budget` seconds or MC_MAX_ITERS, whichever is first.
        All opponents are drawn from `allowed_hands` (falls back to RANGE_TIER).
        Returns (equity, iterations_completed).
        """
        if len(hole_cards) < 2:
            return 0.0, 0

        num_opponents = max(1, min(5, num_opponents))
        if allowed_hands is None:
            allowed_hands = RANGE_TIER.get(max(1, min(4, opp_max_tier)), RANGE_TIER[3])
        dead_cards = set(hole_cards) | set(community_cards)
        available = [c for c in FULL_DECK_INTS if c not in dead_cards]
        cards_to_come = 5 - len(community_cards)

        wins = 0.0
        iterations = 0
        deadline = time.perf_counter() + time_budget

        # Check clock every 64 rollouts; stop at 8k or time budget, whichever first
        while time.perf_counter() < deadline and iterations < MC_MAX_ITERS:
            batch = min(64, MC_MAX_ITERS - iterations)
            for _ in range(batch):
                temp = available[:]
                opp_hands = []
                skip = False
                for _opp in range(num_opponents):
                    h = self.sample_opponent_hand(temp, allowed_hands)
                    if not h:
                        skip = True
                        break
                    opp_hands.append(h)
                    try:
                        temp.remove(h[0])
                        temp.remove(h[1])
                    except ValueError:
                        skip = True
                        break
                if skip or len(temp) < cards_to_come:
                    continue
                extra = random.sample(temp, cards_to_come) if cards_to_come else []
                sim_board = community_cards + extra
                my_score = self.evaluator.evaluate(sim_board, hole_cards)
                best_opp_score = self.evaluator.evaluate(sim_board, opp_hands[0])
                for oh in opp_hands[1:]:
                    score = self.evaluator.evaluate(sim_board, oh)
                    if score < best_opp_score:  # In treys, lower score = stronger hand
                        best_opp_score = score

                if my_score < best_opp_score:
                    wins += 1.0
                elif my_score == best_opp_score:
                    wins += 0.5
                iterations += 1

        equity = (wins / iterations) if iterations > 0 else 0.5
        return equity, iterations

    def format_valid_action(self, desired_action: str, desired_amount: int, valid_actions_list):
        """
        Strictly validates and clamps the chosen action against the server's
        `valid_actions` schema to prevent `action_rejected` errors.
        """
        actions_map = {a["action"]: a for a in valid_actions_list}
        to_call = actions_map.get("call", {}).get("amount", 0)

        if desired_action == "raise":
            if "raise" in actions_map:
                r_info = actions_map["raise"]
                r_min = r_info.get("min", r_info.get("amount", to_call * 2))
                r_max = r_info.get("max", r_min)
                clamped = max(r_min, min(int(desired_amount), r_max))
                return "raise", clamped
            elif "bet" in actions_map:
                b_info = actions_map["bet"]
                b_min = b_info.get("min", b_info.get("amount", 20))
                b_max = b_info.get("max", b_min)
                clamped = max(b_min, min(int(desired_amount), b_max))
                return "bet", clamped
            elif "call" in actions_map:
                return "call", to_call
            elif "check" in actions_map:
                return "check", 0

        if desired_action == "call":
            if "call" in actions_map:
                return "call", to_call
            if "check" in actions_map:
                return "check", 0

        if desired_action == "check":
            if "check" in actions_map:
                return "check", 0
            if to_call == 0 and "call" in actions_map:
                return "call", 0
            return ("fold", 0) if "fold" in actions_map else ("check", 0)

        # Fallback to fold (or check if folding is illegal because checking is free)
        if " check" in actions_map or (to_call == 0 and "check" in actions_map):
            return "check", 0
        if "fold" in actions_map:
            return "fold", 0
        # Ultimate safety fallback: pick first legal action
        first = valid_actions_list[0]
        return first["action"], first.get("amount", first.get("min", 0)) or 0

    def decide(self, state: dict):
        hole_cards = state["hole_cards"]
        community_cards = state["community_cards"]
        pot = state["pot"]
        valid_actions = state["valid_actions"]
        position = state["position"]
        big_blind = state.get("big_blind", 20)
        active_opponents = state.get("active_opponents", 1)
        opp_max_tier = state.get("opp_max_tier", 3)
        plan = state.get("line_plan") or empty_line_plan()
        state["line_plan"] = plan

        actions_map = {a["action"]: a for a in valid_actions}
        to_call = actions_map.get("call", {}).get("amount", 0)
        raise_info = actions_map.get("raise") or actions_map.get("bet") or {}
        min_raise = raise_info.get("min", big_blind * 2)
        max_raise = raise_info.get("max", state.get("stack", 2000))
        effective_stack = max(max_raise, to_call)

        if len(hole_cards) < 2:
            return self.format_valid_action("check", 0, valid_actions), 0.0, 0

        hand_str = cards_to_hand_str(hole_cards[0], hole_cards[1])
        tier = hand_preflop_tier(hand_str)
        in_position = position in ("BTN", "CO")
        pot_odds = to_call / (pot + to_call) if (pot + to_call) > 0 else 0.0
        street = len(community_cards)
        texture = classify_board(community_cards)

        if street == 0 and to_call > big_blind * 4.5:
            allowed_hands = RANGE_VS_3BET
        elif street >= 3 and to_call > pot * 0.65:
            allowed_hands = RANGE_TIER[max(1, min(2, opp_max_tier))]
        else:
            allowed_hands = RANGE_TIER.get(max(1, min(4, opp_max_tier)), RANGE_TIER[3])

        # -----------------------------------------------------------------
        # 1. RUN MONTE CARLO ROLLOUTS (Uses the 45s action window wisely)
        # -----------------------------------------------------------------
        equity, rollouts = self.estimate_equity(
            hole_cards=hole_cards,
            community_cards=community_cards,
            num_opponents=active_opponents,
            opp_max_tier=opp_max_tier,
            time_budget=MC_TIME_BUDGET,
            allowed_hands=allowed_hands,
        )
        adj_equity = max(0.0, equity - 0.02 * max(0, active_opponents - 1))

        def finish(desired_action, desired_amount=0):
            a, amt = self.format_valid_action(desired_action, desired_amount, valid_actions)
            if street >= 3:
                aggressive = a in ("raise", "bet", "all_in")
                if plan.get("line") in (None, "none"):
                    plan["line"] = classify_line(adj_equity)
                if aggressive:
                    plan["streets_bet"] = plan.get("streets_bet", 0) + 1
                    if adj_equity >= 0.66:
                        plan["line"] = "value"
                elif a == "check" and street == 3:
                    plan["flop_checked"] = True
                elif a == "call" and plan.get("line") == "none":
                    plan["line"] = "draw" if adj_equity < 0.66 else "value"
            state["line_plan"] = plan
            return (a, amt), equity, rollouts

        # -----------------------------------------------------------------
        # 2. PRE-FLOP STRATEGY
        # -----------------------------------------------------------------
        if street == 0:
            stack_bb = effective_stack / big_blind if big_blind > 0 else 100
            is_unopened = (to_call <= big_blind)
            pf_margin = 0.02 if in_position else (0.03 if position == "BB" else 0.06)
            pf_required = pot_odds + pf_margin
            pf_stack_ok = to_call <= effective_stack * (0.12 if (in_position or position == "BB") else 0.08)

            if stack_bb <= 14:
                if tier <= 2 or (tier == 3 and position in ("BTN", "SB", "CO")):
                    return finish("raise", max_raise)
                return finish("check" if to_call == 0 else "fold", 0)

            if is_unopened:
                open_size = int(big_blind * 2.5) if to_call <= big_blind else int(pot + big_blind * 2)
                if position in ("UTG", "MP") and tier <= 2:
                    return finish("raise", open_size)
                if position == "CO" and tier <= 3:
                    return finish("raise", open_size)
                if position in ("BTN", "SB") and tier <= 4:
                    return finish("raise", open_size)
                if position == "BB":
                    if tier <= 2:
                        return finish("raise", int(big_blind * 3))
                    return finish("check" if to_call == 0 else "call", 0)
                if position == "SB" and to_call <= big_blind // 2 and tier <= 4:
                    return finish("call", to_call)
                return finish("check" if to_call == 0 else "fold", 0)

            # Facing a 4-bet: continue only with true value
            if to_call > big_blind * 8:
                if hand_str in FOUR_BET_VALUE:
                    return finish("raise", max_raise)
                if tier == 1 and pf_stack_ok:
                    return finish("call", to_call)
                return finish("fold", 0)

            three_bet_size = int(to_call * (3.0 if in_position else 3.5))
            if tier == 1:
                if to_call > big_blind * 4.5 and (
                    hand_str in FOUR_BET_VALUE or to_call >= effective_stack * 0.35
                ):
                    return finish("raise", int(to_call * 2.4))
                if to_call <= big_blind * 4.5:
                    return finish("raise", three_bet_size)
                return finish("call", to_call)
            if to_call <= big_blind * 4.5:
                if tier == 2 and random.random() < 0.35:
                    return finish("raise", three_bet_size)
                if hand_str in THREE_BET_BLUFFS and position in ("BTN", "CO", "SB") and random.random() < 0.20:
                    return finish("raise", three_bet_size)

            if adj_equity >= pf_required and pf_stack_ok and tier <= (3 if (in_position or position == "BB") else 2):
                return finish("call", to_call)
            return finish("fold", 0)

        # -----------------------------------------------------------------
        # 3. POST-FLOP (texture + street plan + pot odds)
        # -----------------------------------------------------------------
        spr = effective_stack / max(1, pot)
        line = plan.get("line") or "none"

        def size_for(line_name):
            if line_name == "air":
                frac = 0.33 if texture["dry"] else 0.55
            elif texture["wet"] or street == 5:
                frac = 0.75 if line_name == "value" else 0.55
            elif texture["dry"]:
                frac = 0.33
            else:
                frac = 0.50
            return int(max(1, pot * frac))

        if to_call == 0:
            if line == "air":
                if street >= 5:
                    return finish("check", 0)
                if texture["dry"] and in_position and plan.get("streets_bet", 0) == 1 and random.random() < 0.30:
                    return finish("raise", size_for("air"))
                return finish("check", 0)
            if line == "draw":
                if adj_equity >= 0.62:
                    return finish("raise", size_for("value"))
                if street == 4 and in_position and adj_equity >= 0.38:
                    return finish("raise", size_for("draw"))
                return finish("check", 0)
            if line == "value" and adj_equity >= 0.55:
                return finish("raise", size_for("value"))

            if adj_equity >= 0.72:
                return finish("raise", size_for("value"))
            if adj_equity >= (0.52 if in_position else 0.60):
                return finish("raise", size_for("value"))
            if street == 3 and in_position and texture["dry"] and adj_equity >= 0.32 and random.random() < 0.70:
                return finish("raise", size_for("air"))
            if street == 3 and in_position and texture["wet"] and adj_equity >= 0.48 and random.random() < 0.40:
                return finish("raise", size_for("draw"))
            if street == 4 and plan.get("flop_checked") and in_position and texture["dry"] and adj_equity >= 0.40:
                return finish("raise", size_for("value"))
            return finish("check", 0)

        street_margin = 0.03 if street == 3 else (0.05 if street == 4 else 0.07)
        if texture["wet"]:
            street_margin += 0.02
        if texture["dry"]:
            street_margin -= 0.01
        pos_margin = 0.0 if in_position else 0.04
        size_margin = 0.03 if to_call > pot * 0.65 else 0.0
        required_equity = pot_odds + street_margin + pos_margin + size_margin

        if line == "air" and adj_equity < required_equity + 0.03:
            return finish("fold", 0)

        if plan.get("flop_checked") and adj_equity >= 0.70 and to_call <= pot * 0.6:
            return finish("raise", int(pot + to_call * 2.2))
        if street == 3 and (not in_position) and adj_equity >= 0.44 and texture["wet"] and to_call <= pot * 0.45 and random.random() < 0.18:
            return finish("raise", int(pot * 0.7 + to_call))

        if adj_equity >= 0.78 or (adj_equity >= 0.68 and spr <= 2.0):
            raise_target = max_raise if spr <= 2.5 else int(pot + to_call * 2.5)
            return finish("raise", raise_target)

        if street == 3 and in_position and to_call <= pot * 0.4 and adj_equity >= max(0.0, pot_odds - 0.02):
            plan["line"] = "draw"
            return finish("call", to_call)

        if adj_equity >= required_equity:
            return finish("call", to_call)

        impl_need = pot_odds - (0.05 if in_position else 0.02)
        if (
            street == 3
            and adj_equity >= impl_need
            and to_call <= pot * (0.55 if in_position else 0.40)
            and spr >= 4.0
        ):
            plan["line"] = "draw"
            return finish("call", to_call)

        return finish("fold", 0)


# =====================================================================
# 5. WEBSOCKET BOT CLIENT WITH RESYNC & STATE TRACKING
# =====================================================================
class OpenPokerClient:
    def __init__(self, api_key: str, ws_url: str):
        self.api_key = api_key
        self.ws_url = ws_url
        self.tracker = OpponentTracker()
        self.engine = ComprehensivePokerEngine(self.tracker)

        self.hole_cards = []
        self.community_cards = []
        self.dealer_seat = 0
        self.my_seat = None
        self.table_id = None
        self.last_table_seq = 0
        self.players = []
        self.folded_seats = set()
        self.last_aggressor_id = None
        self.line_plan = empty_line_plan()

        # Telemetry for the Render status page
        self.hands_played = 0
        self.last_action_summary = "Waiting for first hand..."
        self.connected = False
        self.boot_time = time.time()

    def check_active_game(self):
        """Cold-start discovery per OpenPoker Reconnection spec."""
        headers = {"Authorization": f"Bearer {self.api_key}"}
        try:
            resp = requests.get(f"{REST_BASE_URL}/api/me/active-game", headers=headers, timeout=5)
            if resp.status_code == 200:
                return resp.json()
        except Exception as e:
            print(f"[REST] Active-game check skipped: {e}")
        return None

    def get_my_position(self, my_seat, players) -> str:
        if not players or my_seat is None:
            return "MP"
        seats = sorted([p["seat"] for p in players if "seat" in p])
        if my_seat not in seats:
            return "MP"
        dealer_idx = 0
        for i, s in enumerate(seats):
            if s <= (self.dealer_seat or 0):
                dealer_idx = i
        rotated = seats[dealer_idx:] + seats[:dealer_idx]
        rel = rotated.index(my_seat)
        n = len(seats)
        if n == 2:
            return "BTN" if rel == 0 else "BB"
        if rel == 0:
            return "BTN"
        if rel == 1:
            return "SB"
        if rel == 2:
            return "BB"
        if rel == n - 1:
            return "CO"
        if rel == 3 and n >= 5:
            return "UTG"
        return "MP"

    async def handle_your_turn(self, ws, msg: dict):
        turn_token = msg.get("turn_token")
        if not turn_token:
            return

        hand_id = msg.get("hand_id")
        pot = msg.get("pot", 0)
        valid_actions = msg.get("valid_actions", [])
        if not valid_actions:
            return

        if "community_cards" in msg and msg["community_cards"] is not None:
            self.community_cards = [Card.new(c) for c in msg["community_cards"]]
        if "hole_cards" in msg and msg["hole_cards"]:
            self.hole_cards = [Card.new(c) for c in msg["hole_cards"]]
        if "dealer_seat" in msg or "button_seat" in msg:
            self.dealer_seat = msg.get("dealer_seat", msg.get("button_seat", self.dealer_seat))

        my_seat = msg.get("seat", self.my_seat)
        players = msg.get("players", self.players)
        position = self.get_my_position(my_seat, players)

        if self.line_plan.get("hand_id") != hand_id:
            self.line_plan = empty_line_plan(hand_id)

        # Estimate active opponents and aggressor tightness
        total_players = len(players) if players else 6
        active_opponents = max(1, total_players - len(self.folded_seats) - 1)

        opp_vpip = self.tracker.get_vpip(self.last_aggressor_id) if self.last_aggressor_id else 0.30
        if opp_vpip < 0.18:
            opp_max_tier = 2  # Tight nit
        elif opp_vpip < 0.32:
            opp_max_tier = 3  # Typical regular
        else:
            opp_max_tier = 4  # Loose player

        state = {
            "hole_cards": self.hole_cards,
            "community_cards": self.community_cards,
            "pot": pot,
            "valid_actions": valid_actions,
            "position": position,
            "big_blind": msg.get("big_blind", 20),
            "stack": msg.get("max_raise", msg.get("stack", 2000)),
            "active_opponents": active_opponents,
            "opp_max_tier": opp_max_tier,
            "line_plan": self.line_plan,
        }

        t0 = time.perf_counter()
        # Run heavy Monte Carlo rollouts in a worker thread so the event loop stays responsive
        (action, amount), equity, rollouts = await asyncio.to_thread(self.engine.decide, state)
        self.line_plan = state.get("line_plan", self.line_plan)
        elapsed = time.perf_counter() - t0

        payload = {
            "type": "action",
            "hand_id": hand_id,
            "client_action_id": str(uuid.uuid4()),
            "turn_token": turn_token,
            "action": action,
        }
        if action in ("raise", "bet", "call") and amount and amount > 0:
            payload["amount"] = int(amount)

        await ws.send(json.dumps(payload))

        hc_str = " ".join([Card.int_to_str(c) for c in self.hole_cards]) if self.hole_cards else "??"
        bd_str = " ".join([Card.int_to_str(c) for c in self.community_cards]) if self.community_cards else "Preflop"
        self.last_action_summary = (
            f"[{position}] Cards: {hc_str} | Board: {bd_str} | "
            f"Eq: {equity*100:.1f}% ({rollouts} sims in {elapsed:.2f}s) -> {action.upper()} {amount}"
        )
        print(self.last_action_summary)

    async def run_forever(self):
        headers = {"Authorization": f"Bearer {self.api_key}"}
        header_kwarg = (
            "additional_headers"
            if "additional_headers" in inspect.signature(websockets.connect).parameters
            else "extra_headers"
        )
        backoff = 2

        while True:
            try:
                active = await asyncio.to_thread(self.check_active_game)
                print(f"[Client] Connecting to {self.ws_url}...")

                async with websockets.connect(
                    self.ws_url,
                    ping_interval=20,
                    ping_timeout=20,
                    **{header_kwarg: headers}
                ) as ws:
                    self.connected = True
                    backoff = 2
                    print("[WebSocket] Connected to OpenPoker.")

                    if active and active.get("playing") and active.get("table_id"):
                        self.table_id = active["table_id"]
                        print(f"[Resync] Resuming active table {self.table_id}...")
                        await ws.send(json.dumps({
                            "type": "resync_request",
                            "table_id": self.table_id,
                            "last_table_seq": self.last_table_seq
                        }))
                    else:
                        await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

                    await ws.send(json.dumps({"type": "set_auto_rebuy", "enabled": True}))

                    async for raw_message in ws:
                        msg = json.loads(raw_message)
                        msg_type = msg.get("type")

                        if "table_seq" in msg:
                            self.last_table_seq = max(self.last_table_seq, msg["table_seq"])
                        if "table_id" in msg:
                            self.table_id = msg["table_id"]

                        if msg_type == "connected":
                            print(f"[Server] Authenticated as: {msg.get('name', 'Bot')}")

                        elif msg_type == "error":
                            code = msg.get("code")
                            print(f"[Server Error] {code}: {msg.get('message')}")
                            if code == "already_seated" and msg.get("table_id"):
                                self.table_id = msg["table_id"]
                                await ws.send(json.dumps({
                                    "type": "resync_request",
                                    "table_id": self.table_id,
                                    "last_table_seq": 0
                                }))
                            elif code == "insufficient_season_chips":
                                print("[Bankroll] Low chips detected off-table. Triggering manual rebuy...")
                                await ws.send(json.dumps({"type": "rebuy", "amount": 0}))
                                await asyncio.sleep(2)
                                await ws.send(json.dumps({"type": "join_lobby", "buy_in": 1000}))

                        elif msg_type in ("hand_start", "new_hand"):
                            self.hands_played += 1
                            self.hole_cards = []
                            self.community_cards = []
                            self.folded_seats.clear()
                            self.last_aggressor_id = None
                            self.line_plan = empty_line_plan(msg.get("hand_id"))
                            self.dealer_seat = msg.get("dealer_seat", msg.get("button_seat", 0))
                            self.players = msg.get("players", self.players)
                            self.tracker.start_new_hand(self.players)

                        elif msg_type == "hole_cards":
                            self.hole_cards = [Card.new(c) for c in msg.get("cards", [])]

                        elif msg_type == "community_cards":
                            self.community_cards = [Card.new(c) for c in msg.get("cards", [])]

                        elif msg_type == "player_action":
                            seat = msg.get("seat")
                            act = msg.get("action")
                            pid = msg.get("player_id") or msg.get("name") or str(seat)
                            if act == "fold" and seat is not None:
                                self.folded_seats.add(seat)
                            if act in ("raise", "bet", "all_in"):
                                self.last_aggressor_id = pid
                            self.tracker.record_action(
                                pid=pid,
                                action=act,
                                is_preflop=(len(self.community_cards) == 0)
                            )

                        elif msg_type == "resync_response":
                            snap = msg.get("snapshot", {})
                            if snap.get("community_cards"):
                                self.community_cards = [Card.new(c) for c in snap["community_cards"]]
                            hero = snap.get("hero", {})
                            if hero.get("hole_cards"):
                                self.hole_cards = [Card.new(c) for c in hero["hole_cards"]]
                            if hero.get("turn_token") and hero.get("valid_actions"):
                                turn_msg = {
                                    "turn_token": hero["turn_token"],
                                    "valid_actions": hero["valid_actions"],
                                    "hand_id": snap.get("hand_id"),
                                    "pot": snap.get("pot", 0),
                                    "seat": hero.get("seat"),
                                    "players": snap.get("players", []),
                                }
                                await self.handle_your_turn(ws, turn_msg)

                        elif msg_type == "your_turn":
                            await self.handle_your_turn(ws, msg)

                        elif msg_type == "auto_rebuy_scheduled":
                            wait_sec = msg.get("cooldown_seconds", 300)
                            print(f"[Rebuy] Cooldown active. Waiting {wait_sec}s for 1,500 free chips...")
                            await asyncio.sleep(wait_sec + 2)
                            await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

                        elif msg_type == "rebuy_success":
                            print("[Rebuy] Chips credited! Re-joining lobby...")
                            await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

                        elif msg_type == "busted":
                            print("[Table] Busted! Waiting 3s for instant auto-rebuy...")
                            await asyncio.sleep(3)
                            await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

            except Exception as e:
                self.connected = False
                jitter = random.uniform(0.5, 2.0)
                wait_time = min(60, backoff + jitter)
                print(f"[Disconnected] {e}. Reconnecting in {wait_time:.1f}s...")
                await asyncio.sleep(wait_time)
                backoff = min(60, backoff * 2)


# =====================================================================
# 6. RENDER.COM KEEP-ALIVE WEB SERVER & SELF-PINGER
# =====================================================================
async def start_render_server(bot: OpenPokerClient):
    app = web.Application()

    async def health_handler(request):
        uptime_min = int((time.time() - bot.boot_time) / 60)
        status = {
            "status": "online" if bot.connected else "reconnecting",
            "uptime_minutes": uptime_min,
            "hands_played": bot.hands_played,
            "last_decision": bot.last_action_summary,
            "tracked_opponents": len(bot.tracker.stats),
        }
        return web.json_response(status)

    app.router.add_get("/", health_handler)
    app.router.add_get("/health", health_handler)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()
    print(f"[Render Server] Listening on http://0.0.0.0:{PORT}")

async def self_ping_loop():
    """Pings RENDER_EXTERNAL_URL every 10 minutes so Render's free tier doesn't sleep."""
    await asyncio.sleep(15)
    target_url = f"{RENDER_EXTERNAL_URL.rstrip('/')}/health" if RENDER_EXTERNAL_URL else f"http://127.0.0.1:{PORT}/health"
    async with aiohttp.ClientSession() as session:
        while True:
            try:
                async with session.get(target_url, timeout=10) as resp:
                    print(f"[Keep-Alive] Pinged {target_url} -> HTTP {resp.status}")
            except Exception as e:
                print(f"[Keep-Alive] Ping warning: {e}")
            await asyncio.sleep(600)  # 10 minutes (Render sleeps after 15 mins of no inbound traffic)

async def main():
    bot = OpenPokerClient(api_key=API_KEY, ws_url=WS_URL)
    await start_render_server(bot)
    await asyncio.gather(
        bot.run_forever(),
        self_ping_loop(),
    )

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n[Shutdown] Bot stopped.")
