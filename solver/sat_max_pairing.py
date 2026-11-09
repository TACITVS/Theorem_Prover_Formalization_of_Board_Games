import z3
import re

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
        sublists = re.findall(r"\[(.*?)\]", m.group(1))
        parsed = [[int(x) for x in s.replace(";", " ").split()] for s in sublists]
        lines.extend(parsed)

    return lines

all_lines = load_qubic_board_lines("QubicBoard.v")

# Each line l has 10 possible pairs of cells: (c1, c2) with c1 < c2
# Let binary variable p_{l, c1, c2} indicate that line l is paired using (c1, c2)
opt = z3.Optimize()

pair_vars = {} # (l, c1, c2) -> Bool
cell_incident_pairs = {c: [] for c in range(125)}
line_pairs = {l: [] for l in range(109)}

for l_id, line in enumerate(all_lines):
    for i in range(len(line)):
        for j in range(i + 1, len(line)):
            c1, c2 = line[i], line[j]
            v = z3.Bool(f"p_{l_id}_{c1}_{c2}")
            pair_vars[(l_id, c1, c2)] = v
            line_pairs[l_id].append(v)
            cell_incident_pairs[c1].append(v)
            cell_incident_pairs[c2].append(v)

# Constraint 1: Each line is paired at most once
for l_id in range(109):
    opt.add(z3.AtMost(*line_pairs[l_id], 1))

# Constraint 2: Each cell is used in at most one pair
for c in range(125):
    opt.add(z3.AtMost(*cell_incident_pairs[c], 1))

# Objective: Maximize total paired lines
# Let line_is_paired_l be an indicator for line l
line_indicators = []
for l_id in range(109):
    ind = z3.Bool(f"paired_{l_id}")
    opt.add(ind == z3.Or(line_pairs[l_id]))
    line_indicators.append(z3.If(ind, 1, 0))

total_paired = z3.Sum(line_indicators)
opt.maximize(total_paired)

print("Solving Maximum Disjoint Line-Pairing Capacity on 5^3 hypergraph...")
if opt.check() == z3.sat:
    m = opt.model()
    val = m.eval(total_paired).as_long()
    print(f"==========================================================================")
    print(f"EXACT MAXIMUM DISJOINT LINE-PAIRING CAPACITY: {val} / 109 lines.")
    print(f"==========================================================================")
    print(f"UNPAIRED LINES ON EMPTY BOARD: {109 - val} lines.")
else:
    print("Could not solve.")
