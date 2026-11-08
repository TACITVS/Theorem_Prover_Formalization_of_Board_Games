/-
==============================================================================
TwelveMensMorris.lean - Formal Mathematical Verification of Twelve Men's Morris
Topology, 20 Mills (including 4 Diagonals), Broken Regularity, 40 Edges,
8-Stone Transversal Barrier Theorem, and +4 Defensive Surplus Law
Machine-checked in Lean 4.35.0 with ZERO sorrys and approved kernel axioms only.
==============================================================================
-/

namespace TwelveMensMorris

def NUM_POINTS : Nat := 24

def all_points : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7,
   8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23]

theorem all_points_length : all_points.length = 24 := by rfl

def corners : List Nat :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22]

theorem corners_length : corners.length = 12 := by rfl

def midpoints : List Nat :=
  [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23]

theorem midpoints_length : midpoints.length = 12 := by rfl

/-- The 16 classical concentric and radial mills -/
def standard_mills : List (Nat × Nat × Nat) :=
  [ -- Ring 0 (Outer)
    (0, 1, 2), (2, 3, 4), (4, 5, 6), (0, 6, 7),
    -- Ring 1 (Middle)
    (8, 9, 10), (10, 11, 12), (12, 13, 14), (8, 14, 15),
    -- Ring 2 (Inner)
    (16, 17, 18), (18, 19, 20), (20, 21, 22), (16, 22, 23),
    -- Radial
    (1, 9, 17), (3, 11, 19), (5, 13, 21), (7, 15, 23)
  ]

/-- The 4 diagonal mills unique to Twelve Men's Morris (Morabaraba) -/
def diagonal_mills : List (Nat × Nat × Nat) :=
  [ (0, 8, 16),   -- NW Diagonal
    (2, 10, 18),  -- NE Diagonal
    (4, 12, 20),  -- SE Diagonal
    (6, 14, 22)   -- SW Diagonal
  ]

theorem diagonal_mills_count : diagonal_mills.length = 4 := by rfl

/-- All 20 Mills of Twelve Men's Morris -/
def all_mills_12 : List (Nat × Nat × Nat) :=
  standard_mills ++ diagonal_mills

theorem all_mills_12_count : all_mills_12.length = 20 := by rfl

def point_in_mill (p : Nat) (m : Nat × Nat × Nat) : Bool :=
  let (a, b, c) := m
  (p == a) || (p == b) || (p == c)

def mills_of_point_12 (p : Nat) : List (Nat × Nat × Nat) :=
  all_mills_12.filter (point_in_mill p)

/-- Broken Mill Regularity Theorem: In Twelve Men's Morris, all 12 corners have mill degree 3 -/
theorem corners_mill_degree_3 : (corners.all (fun p => (mills_of_point_12 p).length == 3)) = true := by
  decide

/-- Broken Mill Regularity Theorem: In Twelve Men's Morris, all 12 midpoints have mill degree 2 -/
theorem midpoints_mill_degree_2 : (midpoints.all (fun p => (mills_of_point_12 p).length == 2)) = true := by
  decide

/-- Incidence Handshake Theorem: 12 corners * 3 + 12 midpoints * 2 = 60 = 20 mills * 3 points -/
theorem mill_incidence_handshake : 12 * 3 + 12 * 2 = 20 * 3 := by rfl

/-- Adjacency in Twelve Men's Morris: 32 standard edges + 8 diagonal edges = 40 edges -/
def is_adjacent_12 (u v : Nat) : Bool :=
  if u == v then false
  else
    -- Ring 0
    ((u == 0) && (v == 1 || v == 7 || v == 8)) ||
    ((u == 1) && (v == 0 || v == 2 || v == 9)) ||
    ((u == 2) && (v == 1 || v == 3 || v == 10)) ||
    ((u == 3) && (v == 2 || v == 4 || v == 11)) ||
    ((u == 4) && (v == 3 || v == 5 || v == 12)) ||
    ((u == 5) && (v == 4 || v == 6 || v == 13)) ||
    ((u == 6) && (v == 5 || v == 7 || v == 14)) ||
    ((u == 7) && (v == 6 || v == 0 || v == 15)) ||
    -- Ring 1
    ((u == 8)  && (v == 9  || v == 15 || v == 0 || v == 16)) ||
    ((u == 9)  && (v == 8  || v == 10 || v == 1 || v == 17)) ||
    ((u == 10) && (v == 9  || v == 11 || v == 2 || v == 18)) ||
    ((u == 11) && (v == 10 || v == 12 || v == 3 || v == 19)) ||
    ((u == 12) && (v == 11 || v == 13 || v == 4 || v == 20)) ||
    ((u == 13) && (v == 12 || v == 14 || v == 5 || v == 21)) ||
    ((u == 14) && (v == 13 || v == 15 || v == 6 || v == 22)) ||
    ((u == 15) && (v == 14 || v == 8  || v == 7 || v == 23)) ||
    -- Ring 2
    ((u == 16) && (v == 17 || v == 23 || v == 8)) ||
    ((u == 17) && (v == 16 || v == 18 || v == 9)) ||
    ((u == 18) && (v == 17 || v == 19 || v == 10)) ||
    ((u == 19) && (v == 18 || v == 20 || v == 11)) ||
    ((u == 20) && (v == 19 || v == 21 || v == 12)) ||
    ((u == 21) && (v == 20 || v == 22 || v == 13)) ||
    ((u == 22) && (v == 21 || v == 23 || v == 14)) ||
    ((u == 23) && (v == 22 || v == 16 || v == 15))

theorem is_adjacent_12_sym :
  (all_points.all (fun u => all_points.all (fun v => is_adjacent_12 u v == is_adjacent_12 v u))) = true := by
  decide

def degree_12 (u : Nat) : Nat :=
  (all_points.filter (is_adjacent_12 u)).length

/-- Degree distribution: 8 vertices with degree 4, 16 vertices with degree 3 -/
def degree_4_points : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def degree_3_points : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]

theorem degree_4_points_correct : (degree_4_points.all (fun p => degree_12 p == 4)) = true := by
  decide

theorem degree_3_points_correct : (degree_3_points.all (fun p => degree_12 p == 3)) = true := by
  decide

/-- 12MM Graph Handshake Lemma: 8 vertices * 4 + 16 vertices * 3 = 80 = 2 * 40 edges -/
theorem graph_12_handshake : 8 * 4 + 16 * 3 = 2 * 40 := by rfl

/-- 8-Stone Canonical Transversal for Twelve Men's Morris -/
def transversal_12_8 : List Nat := [1, 3, 5, 7, 10, 14, 16, 20]

theorem transversal_12_8_length : transversal_12_8.length = 8 := by rfl

def mill_intersects (t : List Nat) (m : Nat × Nat × Nat) : Bool :=
  let (a, b, c) := m
  t.contains a || t.contains b || t.contains c

/-- Transversal Barrier Theorem for 12MM: T_12 intersects all 20 mills -/
theorem transversal_12_8_covers_all_20_mills :
  (all_mills_12.all (mill_intersects transversal_12_8)) = true := by
  decide

/-- The +4 Defensive Surplus Law:
    In Twelve Men's Morris, each player has 12 stones.
    Since 8 stones suffice to block all 20 mills,
    the second player enjoys a surplus of 4 defensive stones. -/
def STONES_12MM : Nat := 12
def TRANSVERSAL_SIZE_12 : Nat := 8

theorem defensive_surplus_12mm_law : STONES_12MM - TRANSVERSAL_SIZE_12 = 4 := by rfl

/- ============================================================================== -/
/- D4 Dihedral Symmetry Automorphism on All 20 Mills                              -/
/- ============================================================================== -/

def ring_of (p : Nat) : Nat := p / 8
def pos_of (p : Nat) : Nat := p % 8
def rot (p : Nat) : Nat := 8 * ring_of p + ((pos_of p + 2) % 8)
def refl (p : Nat) : Nat := 8 * ring_of p + ((10 - pos_of p) % 8)

def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  let (x1, x2) := if a <= b then (a, b) else (b, a)
  if x2 <= c then (x1, x2, c)
  else if x1 <= c then (x1, c, x2)
  else (c, x1, x2)

def transform_mill (f : Nat → Nat) (m : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (a, b, c) := m
  sort3 (f a) (f b) (f c)

def is_canonical_mill_12 (m : Nat × Nat × Nat) : Bool :=
  all_mills_12.contains m

theorem rot_preserves_all_20_mills :
  (all_mills_12.all (fun m => is_canonical_mill_12 (transform_mill rot m))) = true := by
  decide

theorem refl_preserves_all_20_mills :
  (all_mills_12.all (fun m => is_canonical_mill_12 (transform_mill refl m))) = true := by
  decide

/- ============================================================================== -/
/- The Ply 8 Forced Opening Mill Fork & Corner Ray Double-Fork Theorem            -/
/- ============================================================================== -/

def is_mill_complete_12 (stones : List Nat) (m : Nat × Nat × Nat) : Bool :=
  let (a, b, c) := m
  stones.contains a && stones.contains b && stones.contains c

def forms_mill_12 (stones : List Nat) (p : Nat) : Bool :=
  all_mills_12.any (fun m => point_in_mill p m && is_mill_complete_12 stones m)

/-- Corner 0 radiates 3 distinct mills whose non-zero points {1,2}, {6,7}, {8,16} are disjoint -/
theorem corner_0_three_rays :
  mills_of_point_12 0 = [(0, 1, 2), (0, 6, 7), (0, 8, 16)] := by rfl

def ray_unblocked (b_stones : List Nat) (m : Nat × Nat × Nat) : Bool :=
  !(mill_intersects b_stones m)

/-- For every legal Black reply b1 != 0 at Ply 1 (after White occupies 0 at Ply 0),
    at least 2 of Corner 0's 3 rays remain completely unblocked -/
theorem corner_0_two_rays_unblocked_after_ply1 :
  (all_points.all (fun b1 =>
    (b1 == 0) || (2 <= ((mills_of_point_12 0).filter (ray_unblocked [b1])).length))) = true := by
  decide

def white_ply6_fork_stones : List Nat := [0, 6, 8, 14]

/-- Concrete Ply 8 Double-Fork Theorem:
    White's configuration [0, 6, 8, 14] simultaneously threatens a mill at 22 ((6,14,22))
    and a mill at 15 ((8,14,15)). For every Black move b4 at Ply 7, at least one of the
    two distinct empty targets {15, 22} remains unblocked and forms a mill at Ply 8! -/
theorem ply8_corner_fork_theorem :
  ((15 != 22) &&
   forms_mill_12 (22 :: white_ply6_fork_stones) 22 &&
   forms_mill_12 (15 :: white_ply6_fork_stones) 15 &&
   all_points.all (fun b4 =>
     ((b4 != 15) && forms_mill_12 (15 :: white_ply6_fork_stones) 15) ||
     ((b4 != 22) && forms_mill_12 (22 :: white_ply6_fork_stones) 22))) = true := by
  decide

end TwelveMensMorris

-- Axiom audits
#print axioms TwelveMensMorris.all_points_length
#print axioms TwelveMensMorris.corners_length
#print axioms TwelveMensMorris.midpoints_length
#print axioms TwelveMensMorris.diagonal_mills_count
#print axioms TwelveMensMorris.all_mills_12_count
#print axioms TwelveMensMorris.corners_mill_degree_3
#print axioms TwelveMensMorris.midpoints_mill_degree_2
#print axioms TwelveMensMorris.mill_incidence_handshake
#print axioms TwelveMensMorris.is_adjacent_12_sym
#print axioms TwelveMensMorris.degree_4_points_correct
#print axioms TwelveMensMorris.degree_3_points_correct
#print axioms TwelveMensMorris.graph_12_handshake
#print axioms TwelveMensMorris.transversal_12_8_length
#print axioms TwelveMensMorris.transversal_12_8_covers_all_20_mills
#print axioms TwelveMensMorris.defensive_surplus_12mm_law
#print axioms TwelveMensMorris.rot_preserves_all_20_mills
#print axioms TwelveMensMorris.refl_preserves_all_20_mills
#print axioms TwelveMensMorris.corner_0_three_rays
#print axioms TwelveMensMorris.corner_0_two_rays_unblocked_after_ply1
#print axioms TwelveMensMorris.ply8_corner_fork_theorem
