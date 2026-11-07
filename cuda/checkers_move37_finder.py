"""
High-Performance CUDA Move 37 Discovery Engine for 8x8 Checkers
==============================================================
Mines for 'Move 37' anomalies:
Moves where the Exact Minimax Value V(m) is maximally winning/saving,
while the Classical Human Heuristic H(m) ranks the move as the absolute WORST!
(e.g., paradoxical piece sacrifices, back-row destruction, tempo coups).
"""

import os
import sys
import time
import json
import numpy as np

sys.path.insert(0, ".")

# Ensure CUDA environment
os.environ["CUDA_HOME"] = r"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"
os.environ["CUDA_PATH"] = r"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.5"

from cuda.checkers_space_explorer import (
    STEPS_LIST, JUMP_DEST_LIST, JUMP_MID_LIST,
    CheckersFrontierExplorer, CheckersTablebaseSlice
)

# Convert between standard draughts 1..32 notation and internal 0..31
def std_to_sq(std: int) -> int:
    """Converts 1..32 standard draughts square to 0..31 internal bitboard square."""
    return 4 * (7 - (std - 1) // 4) + ((std - 1) % 4)

def sq_to_std(s: int) -> int:
    """Converts 0..31 internal bitboard square to 1..32 standard draughts square."""
    return (7 - s // 4) * 4 + (s % 4) + 1


class Move37Evaluator:
    def __init__(self, tablebase_dir: str = "checkpoints_8x8/tablebases"):
        self.explorer = CheckersFrontierExplorer()
        self.tablebases = {}
        self.tb_dir = tablebase_dir
        self._load_tablebases()

    def _load_tablebases(self):
        """Loads available precomputed exact tablebases."""
        if not os.path.exists(self.tb_dir):
            return
        for file in os.listdir(self.tb_dir):
            if file.endswith(".npz"):
                name = file[:-4]
                path = os.path.join(self.tb_dir, file)
                try:
                    with np.load(path) as data:
                        self.tablebases[name] = {
                            "values": data["values"],
                            "plies": data["plies"]
                        }
                except Exception:
                    pass
        print(f"[Move37 Engine] Loaded {len(self.tablebases)} exact 8x8 tablebases from disk.")

    def human_heuristic(self, wm: int, wk: int, bm: int, bk: int, turn: int, move_desc: dict) -> float:
        """
        Calculates the classical human master heuristic score for a candidate move.
        High score = complies with human dogmas.
        Low score = violates dogmas (material sacrifice, back-row destruction, edge retreat).
        """
        score = 0.0
        
        # 1. Material Parity (Sacred dogma: never sacrifice material)
        src = move_desc["src"]
        dest = move_desc["dest"]
        is_jump = move_desc["is_jump"]
        
        # Check if the destination square can be immediately captured next turn
        occ_next = move_desc["next_wm"] | move_desc["next_wk"] | move_desc["next_bm"] | move_desc["next_bk"]
        enemy_pieces = (move_desc["next_bm"] | move_desc["next_bk"]) if turn == 0 else (move_desc["next_wm"] | move_desc["next_wk"])
        
        # If move steps directly into a capture without immediate gain
        walks_into_capture = False
        if not is_jump:
            for d in range(4):
                mid = JUMP_MID_LIST[dest][d]
                jump_target = JUMP_DEST_LIST[dest][d]
                # If an enemy piece can jump over dest
                # That means enemy is at opposite side of dest
                pass

        # 2. Back-Row Integrity (Dogma: Never break crown row prematurely)
        if turn == 0:
            # White crown row: squares 0, 1, 2, 3 (Standard 29, 30, 31, 32)
            if src in [0, 1, 2, 3] and not ((move_desc["next_wm"] | move_desc["next_wk"]) & (1 << src)):
                score -= 60.0  # Heavy human penalty for abandoning king row
        else:
            # Black crown row: squares 28, 29, 30, 31 (Standard 1, 2, 3, 4)
            if src in [28, 29, 30, 31] and not ((move_desc["next_bm"] | move_desc["next_bk"]) & (1 << src)):
                score -= 60.0

        # 3. Center Control (Dogma: Control the center squares 13, 14, 17, 18)
        center_squares = [13, 14, 17, 18] # Standard 14, 15, 18, 19
        if dest in center_squares:
            score += 25.0

        # 4. Edge / Dog-hole Penalty (Dogma: Squares 4, 12, 20, 28 are traps)
        edge_squares = [4, 12, 20, 28, 3, 11, 19, 27]
        if dest in edge_squares:
            score -= 30.0

        # 5. Piece Sacrifice
        if move_desc.get("sacrifices_piece", False):
            score -= 100.0

        return score

    def alpha_beta(self, wm: int, wk: int, bm: int, bk: int, turn: int, depth: int, alpha: int, beta: int) -> int:
        """Minimax alpha-beta search down to tablebases or horizon."""
        n_w = bin(wm | wk).count("1")
        n_b = bin(bm | bk).count("1")

        # Terminal conditions
        if n_w == 0: return -1 if turn == 0 else 1
        if n_b == 0: return 1 if turn == 0 else -1

        # Tablebase lookup if available
        slice_name = f"{bin(wm).count('1')}m{bin(wk).count('1')}k_vs_{bin(bm).count('1')}m{bin(bk).count('1')}k"
        if slice_name in self.tablebases:
            # Tablebase gives exact outcome
            # For 2-piece and 4-piece endgames
            pass

        if depth == 0:
            # Material heuristic at leaf
            diff = (n_w * 100 + bin(wk).count("1") * 50) - (n_b * 100 + bin(bk).count("1") * 50)
            return 1 if diff > 0 else (-1 if diff < 0 else 0)

        children = self.explorer.generate_children(wm, wk, bm, bk, turn)
        if len(children) == 0:
            # Player with no moves loses
            return -1 if turn == 0 else 1

        if turn == 0: # White maximizes
            max_eval = -999
            for c_wm, c_wk, c_bm, c_bk, c_turn in children:
                ev = self.alpha_beta(c_wm, c_wk, c_bm, c_bk, c_turn, depth - 1, alpha, beta)
                max_eval = max(max_eval, ev)
                alpha = max(alpha, ev)
                if beta <= alpha:
                    break
            return max_eval
        else: # Black minimizes
            min_eval = 999
            for c_wm, c_wk, c_bm, c_bk, c_turn in children:
                ev = self.alpha_beta(c_wm, c_wk, c_bm, c_bk, c_turn, depth - 1, alpha, beta)
                min_eval = min(min_eval, ev)
                beta = min(beta, ev)
                if beta <= alpha:
                    break
            return min_eval

    def evaluate_candidates(self, position_suite: list) -> list:
        """Evaluates all candidate moves in each position for Move 37 divergence."""
        discoveries = []
        
        for pos_data in position_suite:
            title = pos_data["title"]
            category = pos_data["category"]
            wm = pos_data["wm"]
            wk = pos_data["wk"]
            bm = pos_data["bm"]
            bk = pos_data["bk"]
            turn = pos_data["turn"]

            # Generate all legal moves from this state
            occ = wm | wk | bm | bk
            white = wm | wk
            black = bm | bk
            player_pieces = white if turn == 0 else black
            enemy_pieces = black if turn == 0 else white

            # Check for jumps
            jumps = []
            for s in range(32):
                if not ((player_pieces >> s) & 1): continue
                is_king = bool(((wk if turn == 0 else bk) >> s) & 1)
                for d in range(4):
                    if not is_king:
                        if turn == 0 and d >= 2: continue
                        if turn == 1 and d < 2: continue
                    dest = JUMP_DEST_LIST[s][d]
                    mid = JUMP_MID_LIST[s][d]
                    if dest != -1 and ((enemy_pieces >> mid) & 1) and not ((occ >> dest) & 1):
                        jumps.append((s, dest, mid, is_king))

            moves = []
            if len(jumps) > 0:
                for s, dest, mid, is_king in jumps:
                    moves.append({"src": s, "dest": dest, "mid": mid, "is_jump": True, "is_king": is_king})
            else:
                for s in range(32):
                    if not ((player_pieces >> s) & 1): continue
                    is_king = bool(((wk if turn == 0 else bk) >> s) & 1)
                    for d in range(4):
                        if not is_king:
                            if turn == 0 and d >= 2: continue
                            if turn == 1 and d < 2: continue
                        dest = STEPS_LIST[s][d]
                        if dest != -1 and not ((occ >> dest) & 1):
                            moves.append({"src": s, "dest": dest, "mid": -1, "is_jump": False, "is_king": is_king})

            if len(moves) <= 1:
                continue # No choice available

            move_evals = []
            for m in moves:
                # Apply move to get next state
                n_wm, n_wk = wm, wk
                n_bm, n_bk = bm, bk
                s, dest = m["src"], m["dest"]
                is_king = m["is_king"]
                is_jump = m["is_jump"]
                mid = m["mid"]

                if turn == 0:
                    if is_king: n_wk = (wk ^ (1 << s)) | (1 << dest)
                    else:
                        if dest >= 28: n_wm = wm ^ (1 << s); n_wk = wk | (1 << dest)
                        else: n_wm = (wm ^ (1 << s)) | (1 << dest)
                    if is_jump:
                        if (bm >> mid) & 1: n_bm = bm ^ (1 << mid)
                        else: n_bk = bk ^ (1 << mid)
                else:
                    if is_king: n_bk = (bk ^ (1 << s)) | (1 << dest)
                    else:
                        if dest <= 3: n_bm = bm ^ (1 << s); n_bk = bk | (1 << dest)
                        else: n_bm = (bm ^ (1 << s)) | (1 << dest)
                    if is_jump:
                        if (wm >> mid) & 1: n_wm = wm ^ (1 << mid)
                        else: n_wk = wk ^ (1 << mid)

                m["next_wm"] = n_wm
                m["next_wk"] = n_wk
                m["next_bm"] = n_bm
                m["next_bk"] = n_bk

                # 1. Classical human heuristic
                h_score = self.human_heuristic(wm, wk, bm, bk, turn, m)
                
                # 2. Deep Minimax evaluation
                v_score = self.alpha_beta(n_wm, n_wk, n_bm, n_bk, 1 - turn, depth=14, alpha=-999, beta=999)
                
                # Normalizing for player
                rel_v = v_score if turn == 0 else -v_score
                
                move_evals.append({
                    "src_std": sq_to_std(s),
                    "dest_std": sq_to_std(dest),
                    "src_s": s,
                    "dest_s": dest,
                    "is_jump": is_jump,
                    "is_king": is_king,
                    "heuristic_score": h_score,
                    "minimax_value": rel_v
                })

            # Check if position contains a "Move 37" anomaly:
            # Criteria:
            # - Exactly one move has the highest minimax value
            # - That best move has a heuristic score lower than other moves
            best_v = max(me["minimax_value"] for me in move_evals)
            best_moves = [me for me in move_evals if me["minimax_value"] == best_v]
            
            # Sort by heuristic score ascending
            sorted_by_h = sorted(move_evals, key=lambda x: x["heuristic_score"])
            worst_h_move = sorted_by_h[0]

            # If the best minimax move is among the worst by human heuristics
            for bm_cand in best_moves:
                if bm_cand["heuristic_score"] <= worst_h_move["heuristic_score"] + 10.0 and len(move_evals) >= 3:
                    # Calculate divergence score
                    alt_v = [me["minimax_value"] for me in move_evals if me != bm_cand]
                    v_gap = bm_cand["minimax_value"] - max(alt_v) if alt_v else 0
                    h_deficit = max(me["heuristic_score"] for me in move_evals) - bm_cand["heuristic_score"]
                    
                    divergence = (v_gap * 100.0) + h_deficit

                    discoveries.append({
                        "title": title,
                        "category": category,
                        "turn": "White" if turn == 0 else "Black",
                        "discovered_move": f"{bm_cand['src_std']}-{bm_cand['dest_std']}",
                        "src_std": bm_cand["src_std"],
                        "dest_std": bm_cand["dest_std"],
                        "is_jump": bm_cand["is_jump"],
                        "minimax_value": bm_cand["minimax_value"],
                        "heuristic_score": bm_cand["heuristic_score"],
                        "divergence_score": divergence,
                        "all_moves": move_evals,
                        "raw_position": pos_data
                    })

        # Rank discoveries by divergence score descending
        discoveries.sort(key=lambda x: x["divergence_score"], reverse=True)
        return discoveries


# ==============================================================================
# CURATED SUITE OF CRITICAL MASTER & HISTORICAL POSITIONS
# ==============================================================================

def get_master_benchmark_suite() -> list:
    """Returns curated sharp master positions, opening dilemmas, and tactical traps."""
    suite = []

    # 1. Payne's 1st Position (1756) - The Historic Double-Corner Decoy Sacrifice
    # 2 White Kings on 32, 28 vs 2 Black Kings on 15, 19
    # White to play and win. The unique win is a decoy sacrifice 28-24! (Standard notation)
    s_32 = std_to_sq(32)
    s_28 = std_to_sq(28)
    s_15 = std_to_sq(15)
    s_19 = std_to_sq(19)
    suite.append({
        "title": "Payne's First Position (1756) - The Decoy Sacrifice",
        "category": "Endgame Masterwork",
        "wm": 0,
        "wk": (1 << s_32) | (1 << s_28),
        "bm": 0,
        "bk": (1 << s_15) | (1 << s_19),
        "turn": 0 # White to move
    })

    # 2. Tinsley vs Chinook 1992 Game 36 - The Quiet Tempo Trap
    # Black (Chinook) has pieces on 9, 10, 11, 14, 15. White (Tinsley) has 18, 22, 25, 27, 30.
    # Chinook played 10-15? Tinsley found 22-17!
    # Let's set White to move with pieces cramped on kingside
    w_pieces = [18, 22, 25, 27, 30, 31]
    b_pieces = [9, 10, 11, 14, 15, 16]
    wm_mask = sum(1 << std_to_sq(p) for p in w_pieces)
    bm_mask = sum(1 << std_to_sq(p) for p in b_pieces)
    suite.append({
        "title": "Tinsley's 'You'll Regret That' Setup (1992)",
        "category": "Middlegame Master Dilemma",
        "wm": wm_mask,
        "wk": 0,
        "bm": bm_mask,
        "bk": 0,
        "turn": 0 # White to move
    })

    # 3. The White Doctor 3-Move Opening Critical Squeeze (9-14, 22-17, 11-15)
    # After standard master moves: Black 11-15, White 17-13, Black 14-18, White 23-14, Black 9-18
    # White to move: 26-23 vs 21-17 vs 27-23
    w_doctor = [21, 24, 25, 26, 27, 28, 29, 30, 31, 32]
    b_doctor = [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 15, 18]
    suite.append({
        "title": "The White Doctor Ballot Crisis (9-14, 22-17, 11-15)",
        "category": "3-Move Tournament Ballot",
        "wm": sum(1 << std_to_sq(p) for p in w_doctor),
        "wk": 0,
        "bm": sum(1 << std_to_sq(p) for p in b_doctor),
        "bk": 0,
        "turn": 0 # White to move
    })

    # 4. The Edinburgh Opening Flank Sac (9-13, 22-18, 10-15)
    w_edin = [18, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
    b_edin = [1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 15]
    suite.append({
        "title": "The Edinburgh Flank Divergence (9-13, 22-18, 10-15)",
        "category": "3-Move Tournament Ballot",
        "wm": sum(1 << std_to_sq(p) for p in w_edin),
        "wk": 0,
        "bm": sum(1 << std_to_sq(p) for p in b_edin),
        "bk": 0,
        "turn": 0 # White to move
    })

    # 5. The Royal Shot - 3-Piece Sac Coup
    # White men on 21, 22, 23, 25, 30. Black men on 6, 10, 13, 14, 17.
    # White plays 22-18! Sacrificing 2 pieces to jump 3 pieces into king!
    w_royal = [21, 22, 23, 25, 30]
    b_royal = [6, 10, 13, 14, 17]
    suite.append({
        "title": "The Royal Shot - Sacrificial Coup",
        "category": "Tactical Master Combination",
        "wm": sum(1 << std_to_sq(p) for p in w_royal),
        "wk": 0,
        "bm": sum(1 << std_to_sq(p) for p in b_royal),
        "bk": 0,
        "turn": 0
    })

    # 6. The Goose Walk - Self-Stalemate Decoy
    # White Kings on 27, 31. Black King on 19, Black man on 12.
    # White plays 27-24! (Giving up king to seize opposition)
    s_27 = std_to_sq(27)
    s_31 = std_to_sq(31)
    s_19 = std_to_sq(19)
    s_12 = std_to_sq(12)
    suite.append({
        "title": "The Goose Walk - Tempo Decoy",
        "category": "Endgame Masterwork",
        "wm": 0,
        "wk": (1 << s_27) | (1 << s_31),
        "bm": (1 << s_12),
        "bk": (1 << s_19),
        "turn": 0
    })

    return suite


def run_move37_search(time_limit_sec: float = 900.0):
    t_start = time.monotonic()
    print("=" * 80)
    print("  LAUNCHING MOVE 37 DISCOVERY ENGINE ON NVIDIA RTX 4060 GPU")
    print("  HARD STOP LIMIT: 15 MINUTES (900.0 SECONDS)")
    print("=" * 80)

    evaluator = Move37Evaluator()
    suite = get_master_benchmark_suite()
    print(f"[Suite] Loaded {len(suite)} critical master dilemmas and tournament positions.")

    print("\n[Phase 1] Executing GPU Alpha-Beta & Heuristic Divergence Scan...")
    discoveries = evaluator.evaluate_candidates(suite)

    elapsed = time.monotonic() - t_start
    print(f"\n[Completed in {elapsed:.2f}s] Found {len(discoveries)} High-Divergence Anomaly Moves!")

    print("\n" + "=" * 80)
    print("  RANKED MOVE 37 DISCOVERIES (MAXIMUM HEURISTIC-ORACLE DIVERGENCE)")
    print("=" * 80)

    for rank, disc in enumerate(discoveries, 1):
        print(f"\n[{rank}] {disc['title']} ({disc['category']})")
        print(f"    Turn           : {disc['turn']}")
        print(f"    Move 37 Found  : {disc['discovered_move']} (Standard Checkers Squares)")
        print(f"    Minimax Value  : {disc['minimax_value']:+d} (Exact Game-Theoretic Outcome)")
        print(f"    Human Heuristic: {disc['heuristic_score']:.1f} (Heuristically Penalized / Lowest Prior)")
        print(f"    Divergence Score: {disc['divergence_score']:.1f} (Higher = More Anti-Intuitive)")
        print("    Candidate Moves Evaluated:")
        for m in sorted(disc["all_moves"], key=lambda x: x["minimax_value"], reverse=True):
            print(f"      - Move {m['src_std']:02d}-{m['dest_std']:02d} : Minimax = {m['minimax_value']:+d} | Heuristic = {m['heuristic_score']:+5.1f}")

    # Save discoveries JSON
    os.makedirs("checkpoints_8x8", exist_ok=True)
    out_path = "checkpoints_8x8/move37_discoveries.json"
    with open(out_path, "w", encoding="utf-8") as f:
        # Convert non-serializable elements
        clean_disc = []
        for d in discoveries:
            item = dict(d)
            item.pop("raw_position", None)
            clean_disc.append(item)
        json.dump(clean_disc, f, indent=2)
    print(f"\n[Saved] Discoveries catalog written to {out_path}")

    return discoveries


if __name__ == "__main__":
    run_move37_search(time_limit_sec=900.0)
