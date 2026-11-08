/-
  Checkers.lean: Machine-Checked Cross-Verifier Mirror of Checkers in Lean 4.35.0
  
  Mirrors the Rocq 9.1 formalization:
  1. 32-Square Lattice Coordinates, Rank/File Projections, Dark Square Parity.
  2. Four Diagonal Step Functions (FL, FR, BL, BR).
  3. Four Constant Jump Vectors (+7, +9, -9, -7).
  4. 180-Degree Board Rotation Symmetry (rot180).
  5. 4x4 Micro-Checkers (8-Square Topology & Rank Invariants).
  
  Zero sorry, completely closed under standard Lean 4 kernel axioms.
-/

def numSquares : Nat := 32

def sqRank (s : Nat) : Nat := s / 4

def sqCol (s : Nat) : Nat :=
  let r := sqRank s
  let c := s % 4
  if r % 2 == 0 then 2 * c + 1 else 2 * c

theorem darkSquareParity : ∀ s < 32, (sqRank s + sqCol s) % 2 = 1 := by decide

theorem sqBounds : ∀ s < 32, sqRank s < 8 ∧ sqCol s < 8 := by decide

def stepFL (s : Nat) : Option Nat :=
  if s < 28 then
    let r := sqRank s
    let c := s % 4
    if r % 2 == 0 then some (s + 4)
    else if 0 < c then some (s + 3) else none
  else none

def stepFR (s : Nat) : Option Nat :=
  if s < 28 then
    let r := sqRank s
    let c := s % 4
    if r % 2 == 0 then
      if c < 3 then some (s + 5) else none
    else some (s + 4)
  else none

def stepBL (s : Nat) : Option Nat :=
  if 4 <= s && s < 32 then
    let r := sqRank s
    let c := s % 4
    if r % 2 == 0 then
      if 0 < c ∧ 5 <= s then some (s - 5) else none
    else some (s - 4)
  else none

def stepBR (s : Nat) : Option Nat :=
  if 4 <= s && s < 32 then
    let r := sqRank s
    let c := s % 4
    if r % 2 == 0 then some (s - 4)
    else if c < 3 then some (s - 3) else none
  else none

def stepFL_valid (s : Nat) : Bool :=
  match stepFL s with
  | some dest => sqRank dest == sqRank s + 1
  | none => true

def stepFR_valid (s : Nat) : Bool :=
  match stepFR s with
  | some dest => sqRank dest == sqRank s + 1
  | none => true

def stepBL_valid (s : Nat) : Bool :=
  match stepBL s with
  | some dest => sqRank s == sqRank dest + 1
  | none => true

theorem stepFL_rank_inc : ∀ s < 32, stepFL_valid s = true := by decide
theorem stepFR_rank_inc : ∀ s < 32, stepFR_valid s = true := by decide
theorem stepBL_rank_dec : ∀ s < 32, stepBL_valid s = true := by decide

def jumpFL (s : Nat) : Option (Nat × Nat) :=
  match stepFL s with
  | some mid => match stepFL mid with
                | some dest => some (mid, dest)
                | none => none
  | none => none

def jumpFR (s : Nat) : Option (Nat × Nat) :=
  match stepFR s with
  | some mid => match stepFR mid with
                | some dest => some (mid, dest)
                | none => none
  | none => none

def jumpBL (s : Nat) : Option (Nat × Nat) :=
  match stepBL s with
  | some mid => match stepBL mid with
                | some dest => some (mid, dest)
                | none => none
  | none => none

def jumpBR (s : Nat) : Option (Nat × Nat) :=
  match stepBR s with
  | some mid => match stepBR mid with
                | some dest => some (mid, dest)
                | none => none
  | none => none

def jumpFL_valid (s : Nat) : Bool :=
  match jumpFL s with
  | some (_, dest) => dest == s + 7 && sqRank dest == sqRank s + 2
  | none => true

def jumpFR_valid (s : Nat) : Bool :=
  match jumpFR s with
  | some (_, dest) => dest == s + 9 && sqRank dest == sqRank s + 2
  | none => true

def jumpBL_valid (s : Nat) : Bool :=
  match jumpBL s with
  | some (_, dest) => dest == s - 9 && sqRank s == sqRank dest + 2
  | none => true

def jumpBR_valid (s : Nat) : Bool :=
  match jumpBR s with
  | some (_, dest) => dest == s - 7 && sqRank s == sqRank dest + 2
  | none => true

theorem jumpFL_all_valid : ∀ s < 32, jumpFL_valid s = true := by decide
theorem jumpFR_all_valid : ∀ s < 32, jumpFR_valid s = true := by decide
theorem jumpBL_all_valid : ∀ s < 32, jumpBL_valid s = true := by decide
theorem jumpBR_all_valid : ∀ s < 32, jumpBR_valid s = true := by decide

def rot180 (s : Nat) : Nat := 31 - s

theorem rot180_involutive : ∀ s < 32, rot180 (rot180 s) = s := by decide

theorem rot180_valid : ∀ s < 32, rot180 s < 32 := by decide

theorem rot180_rank : ∀ s < 32, sqRank (rot180 s) = 7 - sqRank s := by decide

theorem rot180_col : ∀ s < 32, sqCol (rot180 s) = 7 - sqCol s := by decide

-- 4x4 Micro-Checkers
def microRank (s : Nat) : Nat := s / 2

def microCol (s : Nat) : Nat :=
  match s with
  | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2
  | 4 => 1 | 5 => 3 | 6 => 0 | 7 => 2
  | _ => 0

theorem microBounds : ∀ s < 8, microRank s < 4 ∧ microCol s < 4 := by decide

theorem microParity : ∀ s < 8, (microRank s + microCol s) % 2 = 1 := by decide

-- Kernel Axiom Audit for all 15 Theorems
#print axioms darkSquareParity
#print axioms sqBounds
#print axioms stepFL_rank_inc
#print axioms stepFR_rank_inc
#print axioms stepBL_rank_dec
#print axioms jumpFL_all_valid
#print axioms jumpFR_all_valid
#print axioms jumpBL_all_valid
#print axioms jumpBR_all_valid
#print axioms rot180_involutive
#print axioms rot180_valid
#print axioms rot180_rank
#print axioms rot180_col
#print axioms microBounds
#print axioms microParity
