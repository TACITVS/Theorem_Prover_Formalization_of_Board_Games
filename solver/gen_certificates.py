"""Generate concrete data for QubicGame.v.

Nothing produced here is trusted: every certificate is re-checked by the
verified boolean checker inside Rocq (`check_sound`, `paircertb_sound`).
This script only *searches* for witnesses.
"""
import re, sys, itertools

def load_lines(path="QubicBoard.v"):
    text = open(path).read()
    out = []
    for name in ["ortho_x_lines", "ortho_y_lines", "ortho_z_lines",
                 "diag_xy_lines", "diag_xz_lines", "diag_yz_lines", "space_diag_lines"]:
        m = re.search(r"Definition\s+" + name + r"\s*:\s*list\s*\(list\s+cell\)\s*:=\s*\[(.*?)\]\.", text, re.S)
        out += [[int(v) for v in s.replace(";", " ").split()] for s in re.findall(r"\[(.*?)\]", m.group(1))]
    assert len(out) == 109
    return out

LINES = load_lines()
STONES = [0, 91, 83, 29, 81, 48, 31, 39, 40, 86, 60, 88, 12, 113, 22, 100, 104]
SCHED = [(1,5,6),(3,15,16),(10,50,51),(11,55,59),(13,65,69),(14,70,73),(15,75,79),(19,95,96),
         (21,108,106),(23,115,118),(24,120,121),(26,1,11),(28,13,8),(29,14,9),(32,27,47),(36,61,71),
         (37,52,57),(38,53,63),(39,54,64),(40,80,85),(42,87,97),(44,89,84),(46,101,116),(47,107,117),
         (51,26,76),(52,2,77),(53,28,78),(55,30,105),(57,7,82),(59,34,109),(67,17,92),(68,18,68),
         (69,19,44),(70,20,45),(71,21,46),(74,24,49),(79,74,56),(80,66,58),(91,93,67),(93,72,98),
         (99,32,122),(101,3,123),(103,4,94)]

def completes(S):
    S = set(S)
    return any(all(c in S for c in l) for l in LINES)

def matching(W, B):
    """Return a list of disjoint pairs covering every line with no Black stone, or None."""
    Wset, Bset = set(W), set(B)
    openl = [l for l in LINES if not (set(l) & Bset)]
    free = [c for c in range(125) if c not in Wset and c not in Bset]
    if 2 * len(openl) > len(free):
        return None
    # bipartite: left = (line, slot), right = free cells
    left = [(i, s) for i in range(len(openl)) for s in range(2)]
    adj = [[c for c in openl[i] if c not in Wset and c not in Bset] for (i, s) in left]
    match_r = {}
    def try_k(u, seen):
        for v in adj[u]:
            if v in seen:
                continue
            seen.add(v)
            if v not in match_r or try_k(match_r[v], seen):
                match_r[v] = u
                return True
        return False
    sys.setrecursionlimit(10000)
    for u in range(len(left)):
        if not try_k(u, set()):
            return None
    byline = {}
    for v, u in match_r.items():
        byline.setdefault(left[u][0], []).append(v)
    return [tuple(sorted(byline[i])) for i in range(len(openl))]

if __name__ == "__main__":
    pair_cells = [c for (_, a, b) in SCHED for c in (a, b)]
    left = [c for c in range(125) if c not in pair_cells and c not in STONES]
    print("leftover cells (22 expected):", len(left), left)
    print("Black 17 stones complete a line?", completes(STONES))
    # choose 17 White cells among the leftovers with no completed line
    for W in itertools.combinations(left, 17):
        if not completes(W):
            break
    print("White witness:", list(W), "completes?", completes(W))
    # legal interleaving check (prefixes of non-completing sets never complete)
    print("Matching for 17/17 position exists?", matching(W, STONES) is not None)

    # Round-16 position: drop Black's last stone and White's last stone,
    # then for every legal White move find a Black reply with a pairing certificate.
    W16, B16 = list(W[:-1]), STONES[:-1]
    branches, bad = [], []
    for x in range(125):
        if x in W16 or x in B16:
            continue
        Wx = W16 + [x]
        if completes(Wx):
            bad.append((x, "white completes"))
            continue
        found = None
        for y in range(125):
            if y in Wx or y in B16:
                continue
            P = matching(Wx, B16 + [y])
            if P is not None:
                found = (y, P)
                break
        if found is None:
            bad.append((x, "no reply"))
        else:
            branches.append((x, found[0], found[1]))
    print("round-16 branches:", len(branches), "bad:", bad[:5], len(bad))
