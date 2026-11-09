import z3

# Generate all 109 lines in 5x5x5
def cell_index(x, y, z):
    return x * 25 + y * 5 + z

all_lines = []
# 75 Orthogonal
for x in range(5):
    for y in range(5):
        all_lines.append([cell_index(x, y, z) for z in range(5)])
for x in range(5):
    for z in range(5):
        all_lines.append([cell_index(x, y, z) for y in range(5)])
for y in range(5):
    for z in range(5):
        all_lines.append([cell_index(x, y, z) for x in range(5)])

# 30 Planar Diagonals
for z in range(5):
    all_lines.append([cell_index(i, i, z) for i in range(5)])
    all_lines.append([cell_index(i, 4 - i, z) for i in range(5)])
for y in range(5):
    all_lines.append([cell_index(i, y, i) for i in range(5)])
    all_lines.append([cell_index(i, y, 4 - i) for i in range(5)])
for x in range(5):
    all_lines.append([cell_index(x, i, i) for i in range(5)])
    all_lines.append([cell_index(x, i, 4 - i) for i in range(5)])

# 4 Space Diagonals
all_lines.append([cell_index(i, i, i) for i in range(5)])
all_lines.append([cell_index(i, i, 4 - i) for i in range(5)])
all_lines.append([cell_index(i, 4 - i, i) for i in range(5)])
all_lines.append([cell_index(i, 4 - i, 4 - i) for i in range(5)])

print(f"Total lines generated: {len(all_lines)}")

# Create Z3 optimizer to find minimum transversal
opt = z3.Optimize()
x = [z3.Bool(f"c_{i}") for i in range(125)]

# Every line must contain at least one chosen cell
for idx, line in enumerate(all_lines):
    opt.add(z3.Or([x[c] for c in line]))

# Objective: Minimize number of cells
total_cells = z3.Sum([z3.If(x[i], 1, 0) for i in range(125)])
opt.minimize(total_cells)

if opt.check() == z3.sat:
    m = opt.model()
    chosen = [i for i in range(125) if z3.is_true(m[x[i]])]
    print(f"EXACT Minimum Transversal Number tau(5^3) = {len(chosen)} cells!")
    print(f"Optimal Transversal Cells: {chosen}")
    # Verify every line is blocked
    for idx, line in enumerate(all_lines):
        assert any(c in chosen for c in line), f"Line {idx} not blocked!"
    print("ALL 109 lines verified 100% blocked by these cells!")
else:
    print("UNSAT - could not solve")
