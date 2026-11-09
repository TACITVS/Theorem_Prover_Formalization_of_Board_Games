import re
import z3

def load_qubic_board_lines(filepath="QubicBoard.v"):
    with open(filepath, "r") as f:
        text = f.read()

    lines = []
    line_groups = [
        "ortho_x_lines",
        "ortho_y_lines",
        "ortho_z_lines",
        "diag_xy_lines",
        "diag_xz_lines",
        "diag_yz_lines",
        "space_diag_lines",
    ]
    for name in line_groups:
        pattern = r"Definition\s+" + name + r"\s*:\s*list\s*\(list\s+cell\)\s*:=\s*\[(.*?)\]\."
        m = re.search(pattern, text, re.DOTALL)
        assert m, f"Failed to find {name} in {filepath}"
        sublists = re.findall(r"\[(.*?)\]", m.group(1))
        parsed = [[int(x) for x in s.replace(";", " ").split()] for s in sublists]
        lines.extend(parsed)

    assert len(lines) == 109, f"Expected 109 lines, got {len(lines)}"
    return lines

# Load lines directly from Rocq 9.1 master board definition
all_lines = load_qubic_board_lines("QubicBoard.v")

# The EXACT 17 Black defense stones certified in QubicTheorem.v
black_defense_stones = [
    0, 91, 83, 29, 81, 48, 31, 39, 40, 86, 60, 88, 12, 113, 22, 100, 104
]

# The EXACT 43 Pairing schedule certified in QubicTheorem.v: (line_id, c1, c2)
pairing_schedule = [
    (1, 5, 6),
    (3, 15, 16),
    (10, 50, 51),
    (11, 55, 59),
    (13, 65, 69),
    (14, 70, 73),
    (15, 75, 79),
    (19, 95, 96),
    (21, 108, 106),
    (23, 115, 118),
    (24, 120, 121),
    (26, 1, 11),
    (28, 13, 8),
    (29, 14, 9),
    (32, 27, 47),
    (36, 61, 71),
    (37, 52, 57),
    (38, 53, 63),
    (39, 54, 64),
    (40, 80, 85),
    (42, 87, 97),
    (44, 89, 84),
    (46, 101, 116),
    (47, 107, 117),
    (51, 26, 76),
    (52, 2, 77),
    (53, 28, 78),
    (55, 30, 105),
    (57, 7, 82),
    (59, 34, 109),
    (67, 17, 92),
    (68, 18, 68),
    (69, 19, 44),
    (70, 20, 45),
    (71, 21, 46),
    (74, 24, 49),
    (79, 74, 56),
    (80, 66, 58),
    (91, 93, 67),
    (93, 72, 98),
    (99, 32, 122),
    (101, 3, 123),
    (103, 4, 94)
]

print("==========================================================================")
print("=== EXACT Z3 SMT VERIFICATION OF QUIBICTHEOREM.V SCHEDULE ===")
print("==========================================================================")
print(f"Total Winning Lines: {len(all_lines)}")
print(f"Black Defense Stones: {len(black_defense_stones)}")
print(f"Paired Lines: {len(pairing_schedule)}")

# Check 1: Pair containment on respective lines
for l_id, c1, c2 in pairing_schedule:
    line = all_lines[l_id]
    assert c1 in line, f"Cell {c1} not in line {l_id}: {line}"
    assert c2 in line, f"Cell {c2} not in line {l_id}: {line}"
    assert c1 != c2, f"Pair cells identical: {c1} == {c2}"
print("[PASS] Check 1: All 43 pairs lie on their respective lines with distinct endpoints.")

# Check 2: Pairwise disjointness of all 86 paired cells
all_pair_cells = []
for _, c1, c2 in pairing_schedule:
    all_pair_cells.extend([c1, c2])

assert len(all_pair_cells) == 86
assert len(set(all_pair_cells)) == 86, "Pair cells overlap!"
print("[PASS] Check 2: All 86 paired cells are 100% pairwise disjoint (No duplicate cells).")

# Check 3: Disjointness between paired cells and defense stones
overlap = set(all_pair_cells).intersection(set(black_defense_stones))
assert len(overlap) == 0, f"Overlap between pairs and defense stones: {overlap}"
print("[PASS] Check 3: Zero overlap between paired cells and defense stones (86 + 17 = 103 disjoint cells).")

# Check 4: Complete 109-line coverage
blocked_by_stone = set()
for l_id, line in enumerate(all_lines):
    if any(s in line for s in black_defense_stones):
        blocked_by_stone.add(l_id)

paired_lines = set(p[0] for p in pairing_schedule)
covered_lines = blocked_by_stone.union(paired_lines)

print(f"Lines blocked by defense stones: {len(blocked_by_stone)}")
print(f"Lines in pairing schedule: {len(paired_lines)}")
print(f"Total lines covered: {len(covered_lines)} / {len(all_lines)}")
assert len(covered_lines) == 109, f"Only {len(covered_lines)} lines covered!"
print("[PASS] Check 4: Exactly 109 / 109 lines are completely covered!")

# Check 5: Z3 SMT Proof of Universal White Blockade
# Propositional variables: w_i is True iff White occupies cell i
solver = z3.Solver()
w = [z3.Bool(f"w_{i}") for i in range(125)]

# Constraint 1 (Defense Stones): White cannot occupy any of Black's 17 defense stones
for s in black_defense_stones:
    solver.add(z3.Not(w[s]))

# Constraint 2 (Pairing Strategy): White cannot occupy both cells in any pair
for _, c1, c2 in pairing_schedule:
    solver.add(z3.Not(z3.And(w[c1], w[c2])))

# Target Assertion: White achieves 5-in-a-row on AT LEAST ONE of the 109 lines
white_line_completions = []
for l_id, line in enumerate(all_lines):
    white_line_completions.append(z3.And([w[c] for c in line]))

solver.add(z3.Or(white_line_completions))

res = solver.check()
print(f"\nZ3 SMT Satisfiability Result: {res}")
if res == z3.unsat:
    print("==========================================================================")
    print(">>> UNREFUTABLE SMT PROOF: Z3 CERTIFIES UNSAT!                          <<<")
    print(">>> WHITE CANNOT COMPLETE ANY OF THE 109 WINNING LINES UNDER THIS POLICY<<<")
    print("==========================================================================")
else:
    print("Counterexample found:", solver.model())
    raise RuntimeError("Verification failed: Model found where White wins!")
