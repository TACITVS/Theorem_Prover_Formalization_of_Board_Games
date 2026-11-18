/-!
# MNKGames.lean: Lean 4 Cross-Check of the (m, n, k) Development

Independent Lean 4 re-verification of the computational core of the Rocq
development (see `../MNK_MATHEMATICAL_MONOGRAPH.md` for the full statement list):

1. Line-counting formula L(m, n, k), an explicit geometric line generator
   `genLines`, and landmark instances (generated count = formula).
2. Strong (maker-maker) game semantics `ForcesWin` and a SOUND certificate
   checker `checkCert`, with the soundness theorem `checkCert_sound`.
   (The previous checker ignored Player 2's own lines and accepted
   board-filling non-winning moves.)
3. (3, 4, 3): the original 132-node certificate re-checked under the corrected
   rules, giving `ForcesWin (genLines 3 4 3) .P1 4 empty` (win within 7 plies).
4. A machine-checked refutation of the former "Subgrid Monotone Projection"
   argument on 3 x 5.
5. The three window certificates (3 x 4 strip, 4 x 3 strip, 4 x 4 corner) are
   re-checked by an independent implementation of the window checker.  The
   lifting theorem that turns them into forced wins on EVERY larger board
   (`window_certificate_lifts`), the (3, 3, 3) draw, the pairing-strategy draws
   and the complete (m, n, 3) characterization are proved in Rocq
   (MNKWindow.v, MNKPairing.v, MNKPhaseTransition.v), not in this file.

Zero `sorry`, zero custom axioms.
-/

inductive Player : Type where
  | P1 : Player
  | P2 : Player
deriving Repr, DecidableEq

def otherPlayer (p : Player) : Player :=
  match p with
  | Player.P1 => Player.P2
  | Player.P2 => Player.P1

theorem otherPlayer_involutive (p : Player) : otherPlayer (otherPlayer p) = p := by
  cases p <;> rfl

-- ============================================================================
-- Section 1: Coordinate Geometry, Line Generator & Line Counting
-- ============================================================================

def coordToIdx (n r c : Nat) : Nat :=
  r * n + c

def idxToRow (n idx : Nat) : Nat :=
  idx / n

def idxToCol (n idx : Nat) : Nat :=
  idx % n

def horizLinesCount (m n k : Nat) : Nat :=
  if k <= n then m * (n - k + 1) else 0

def vertLinesCount (m n k : Nat) : Nat :=
  if k <= m then n * (m - k + 1) else 0

def diag1LinesCount (m n k : Nat) : Nat :=
  if k <= m && k <= n then (m - k + 1) * (n - k + 1) else 0

def diag2LinesCount (m n k : Nat) : Nat :=
  if k <= m && k <= n then (m - k + 1) * (n - k + 1) else 0

def totalLinesFormula (m n k : Nat) : Nat :=
  horizLinesCount m n k + vertLinesCount m n k +
  diag1LinesCount m n k + diag2LinesCount m n k

inductive Direction where
  | dh | dv | dd | da
deriving Repr, DecidableEq

/-- i-th cell (row, column) of the line of direction `d` with bounding-box corner (r, c). -/
def cellAt (k : Nat) : Direction → Nat → Nat → Nat → Nat × Nat
  | .dh, r, c, i => (r, c + i)
  | .dv, r, c, i => (r + i, c)
  | .dd, r, c, i => (r + i, c + i)
  | .da, r, c, i => (r + (k - 1 - i), c + i)

def mkLine (n k : Nat) (d : Direction) (r c : Nat) : List Nat :=
  (List.range k).map (fun i => (cellAt k d r c i).1 * n + (cellAt k d r c i).2)

def gridStarts (a b : Nat) : List (Nat × Nat) :=
  (List.range a).flatMap (fun r => (List.range b).map (fun c => (r, c)))

def starts (m n k : Nat) : Direction → List (Nat × Nat)
  | .dh => if k ≤ n then gridStarts m (n - k + 1) else []
  | .dv => if k ≤ m then gridStarts (m - k + 1) n else []
  | .dd => if k ≤ m && k ≤ n then gridStarts (m - k + 1) (n - k + 1) else []
  | .da => if k ≤ m && k ≤ n then gridStarts (m - k + 1) (n - k + 1) else []

/-- All winning lines of the m x n board with threshold k (same order as in Rocq). -/
def genLines (m n k : Nat) : List (List Nat) :=
  [Direction.dh, .dv, .dd, .da].flatMap
    (fun d => (starts m n k d).map (fun rc => mkLine n k d rc.1 rc.2))

theorem mnk_3_3_3_lines : totalLinesFormula 3 3 3 = 8 := by rfl
theorem mnk_3_4_3_lines : totalLinesFormula 3 4 3 = 14 := by rfl
theorem mnk_4_4_4_lines : totalLinesFormula 4 4 4 = 10 := by rfl
theorem mnk_5_4_4_lines : totalLinesFormula 5 4 4 = 17 := by rfl
theorem mnk_6_4_4_lines : totalLinesFormula 6 4 4 = 24 := by rfl
theorem mnk_7_4_4_lines : totalLinesFormula 7 4 4 = 31 := by rfl
theorem mnk_8_4_4_lines : totalLinesFormula 8 4 4 = 38 := by rfl
theorem mnk_5_5_4_lines : totalLinesFormula 5 5 4 = 28 := by rfl
theorem mnk_8_8_5_lines : totalLinesFormula 8 8 5 = 96 := by rfl
theorem mnk_15_15_5_lines : totalLinesFormula 15 15 5 = 572 := by rfl

-- The generator really produces L(m, n, k) lines on landmark boards.
theorem genLines_count_3_3_3 : (genLines 3 3 3).length = totalLinesFormula 3 3 3 := by decide
theorem genLines_count_3_4_3 : (genLines 3 4 3).length = totalLinesFormula 3 4 3 := by decide
theorem genLines_count_5_4_4 : (genLines 5 4 4).length = totalLinesFormula 5 4 4 := by decide
theorem genLines_count_8_8_5 : (genLines 8 8 5).length = totalLinesFormula 8 8 5 := by decide

theorem mnk_prime_triple_7_5_3_lines : totalLinesFormula 7 5 3 = 76 := by rfl
theorem mnk_prime_triple_11_7_5_lines : totalLinesFormula 11 7 5 = 124 := by rfl
theorem mnk_prime_triple_13_11_7_lines : totalLinesFormula 13 11 7 = 212 := by rfl
theorem mnk_prime_triple_11_7_7_lines : totalLinesFormula 11 7 7 = 56 := by rfl
theorem mnk_prime_triple_17_13_11_lines : totalLinesFormula 17 13 11 = 184 := by rfl
theorem mnk_prime_triple_19_17_13_lines : totalLinesFormula 19 17 13 = 284 := by rfl

-- Arithmetic hypothesis |E| < 2^(k-1) of the Erdos-Selfridge criterion ONLY.
-- The game-theoretic conclusion (draw) is a cited classical theorem, not formalized.
theorem mnk_prime_triple_11_7_7_erdos_bound : totalLinesFormula 11 7 7 < 2^(7 - 1) := by decide
theorem mnk_prime_triple_17_13_11_erdos_bound : totalLinesFormula 17 13 11 < 2^(11 - 1) := by decide
theorem mnk_prime_triple_19_17_13_erdos_bound : totalLinesFormula 19 17 13 < 2^(13 - 1) := by decide

def lines_3_3_3 : List (List Nat) :=
  [ [0, 1, 2], [3, 4, 5], [6, 7, 8],
    [0, 3, 6], [1, 4, 7], [2, 5, 8],
    [0, 4, 8], [2, 4, 6] ]

theorem lines_3_3_3_count : lines_3_3_3.length = 8 := by rfl

def lines_3_4_3 : List (List Nat) :=
  [ [0, 1, 2], [1, 2, 3],
    [4, 5, 6], [5, 6, 7],
    [8, 9, 10], [9, 10, 11],
    [0, 4, 8], [1, 5, 9], [2, 6, 10], [3, 7, 11],
    [0, 5, 10], [1, 6, 11],
    [8, 5, 2], [9, 6, 3] ]

theorem lines_3_4_3_count : lines_3_4_3.length = 14 := by rfl

/-- The hand-written 3 x 4 hypergraph is exactly the generated one. -/
theorem lines_3_4_3_generated : genLines 3 4 3 = lines_3_4_3 := by decide

-- ============================================================================
-- Section 2: Board State & Winning Conditions
-- ============================================================================

abbrev Board := List (Option Player)

def getCell (b : Board) (idx : Nat) : Option Player :=
  b.getD idx none

def setCell (b : Board) (idx : Nat) (p : Player) : Board :=
  match b, idx with
  | [], _ => []
  | _ :: tl, 0 => some p :: tl
  | hd :: tl, idx' + 1 => hd :: setCell tl idx' p

def isCellEmpty (b : Board) (idx : Nat) : Bool :=
  match getCell b idx with
  | none => true
  | some _ => false

def isLegalMove (b : Board) (idx : Nat) : Bool :=
  idx < b.length && isCellEmpty b idx

def cellOwnedBy (b : Board) (p : Player) (idx : Nat) : Bool :=
  match getCell b idx with
  | some q => q == p
  | none => false

def lineOwnedBy (b : Board) (p : Player) (line : List Nat) : Bool :=
  line.all (cellOwnedBy b p)

def checkWin (b : Board) (p : Player) (lines : List (List Nat)) : Bool :=
  lines.any (lineOwnedBy b p)

def legalMoves (b : Board) : List Nat :=
  (List.range b.length).filter (isCellEmpty b)

theorem mem_legalMoves {b : Board} {x : Nat} : x ∈ legalMoves b ↔ isLegalMove b x = true := by
  unfold legalMoves isLegalMove
  simp [List.mem_filter, List.mem_range]

def emptyBoard (n : Nat) : Board := List.replicate n none

-- ============================================================================
-- Section 3: Strong-Game Semantics and a Sound Certificate Checker
-- ============================================================================

/-- `ForcesWin lines p d b`: player `p`, to move on `b`, completes a line within
    `d` of its own moves against every legal reply, and the opponent never
    completes a line first; a non-winning move that fills the board is a draw. -/
inductive ForcesWin (lines : List (List Nat)) (p : Player) : Nat → Board → Prop where
  | now (d : Nat) (b : Board) (m : Nat) :
      isLegalMove b m = true →
      checkWin (setCell b m p) p lines = true →
      ForcesWin lines p (d + 1) b
  | next (d : Nat) (b : Board) (m : Nat) :
      isLegalMove b m = true →
      (∃ c, isLegalMove (setCell b m p) c = true) →
      (∀ c, isLegalMove (setCell b m p) c = true →
        checkWin (setCell (setCell b m p) c (otherPlayer p)) (otherPlayer p) lines = false) →
      (∀ c, isLegalMove (setCell b m p) c = true →
        ForcesWin lines p d (setCell (setCell b m p) c (otherPlayer p))) →
      ForcesWin lines p (d + 1) b

inductive WinCert : Type where
  | imm : Nat → WinCert
  | branch : Nat → List (Nat × WinCert) → WinCert

def findBranch (c : Nat) : List (Nat × WinCert) → Option WinCert
  | [] => none
  | (c', cert') :: tl => if c == c' then some cert' else findBranch c tl

theorem findBranch_mem : ∀ (bs : List (Nat × WinCert)) (c : Nat) (sub : WinCert),
    findBranch c bs = some sub → (c, sub) ∈ bs
  | [], _, _, h => by simp [findBranch] at h
  | (c', s) :: tl, c, sub, h => by
      by_cases hc : c = c'
      · subst hc
        simp [findBranch] at h
        subst h
        exact List.mem_cons_self
      · simp [findBranch, hc] at h
        exact List.mem_cons_of_mem _ (findBranch_mem tl c sub h)

mutual
  def checkCert (lines : List (List Nat)) (p : Player) : Nat → Board → WinCert → Bool
    | 0, _, _ => false
    | _ + 1, b, WinCert.imm m =>
        isLegalMove b m && checkWin (setCell b m p) p lines
    | d + 1, b, WinCert.branch m branches =>
        isLegalMove b m &&
        !(legalMoves (setCell b m p)).isEmpty &&
        (legalMoves (setCell b m p)).all (fun c => (findBranch c branches).isSome) &&
        checkBranches lines p d (setCell b m p) branches

  def checkBranches (lines : List (List Nat)) (p : Player) (d : Nat) (b1 : Board) :
      List (Nat × WinCert) → Bool
    | [] => true
    | (c, nextCert) :: rest =>
        isLegalMove b1 c &&
        !(checkWin (setCell b1 c (otherPlayer p)) (otherPlayer p) lines) &&
        checkCert lines p d (setCell b1 c (otherPlayer p)) nextCert &&
        checkBranches lines p d b1 rest
end

theorem checkBranches_spec (lines : List (List Nat)) (p : Player) (d : Nat) (b1 : Board)
    (ih : ∀ b ct, checkCert lines p d b ct = true → ForcesWin lines p d b) :
    ∀ (bs : List (Nat × WinCert)), checkBranches lines p d b1 bs = true →
      ∀ c sub, (c, sub) ∈ bs →
        isLegalMove b1 c = true ∧
        checkWin (setCell b1 c (otherPlayer p)) (otherPlayer p) lines = false ∧
        ForcesWin lines p d (setCell b1 c (otherPlayer p))
  | [], _, _, _, hm => by simp at hm
  | (c', s) :: rest, h, c, sub, hm => by
      simp only [checkBranches, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨hl, hn⟩, hs⟩, hr⟩ := h
      rcases List.mem_cons.mp hm with he | he
      · cases he
        exact ⟨hl, hn, ih _ _ hs⟩
      · exact checkBranches_spec lines p d b1 ih rest hr c sub he

/-- Soundness: every accepted certificate is a genuine forced win. -/
theorem checkCert_sound (lines : List (List Nat)) (p : Player) :
    ∀ d b ct, checkCert lines p d b ct = true → ForcesWin lines p d b := by
  intro d
  induction d with
  | zero => intro b ct h; cases ct <;> simp [checkCert] at h
  | succ d ih =>
    intro b ct h
    cases ct with
    | imm m =>
      simp only [checkCert, Bool.and_eq_true] at h
      exact ForcesWin.now d b m h.1 h.2
    | branch m bs =>
      simp only [checkCert, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨hm, hne⟩, hcov⟩, hbr⟩ := h
      have spec := checkBranches_spec lines p d (setCell b m p) ih bs hbr
      have reply : ∀ c, isLegalMove (setCell b m p) c = true → ∃ sub, (c, sub) ∈ bs := by
        intro c hc
        have hk := (List.all_eq_true.mp hcov) c (mem_legalMoves.mpr hc)
        obtain ⟨sub, hsub⟩ := Option.isSome_iff_exists.mp hk
        exact ⟨sub, findBranch_mem bs c sub hsub⟩
      refine ForcesWin.next d b m hm ?_ ?_ ?_
      · cases hl : legalMoves (setCell b m p) with
        | nil => rw [hl] at hne; simp at hne
        | cons c _ =>
          exact ⟨c, mem_legalMoves.mp (by rw [hl]; exact List.mem_cons_self)⟩
      · intro c hc
        obtain ⟨sub, hs⟩ := reply c hc
        exact (spec c sub hs).2.1
      · intro c hc
        obtain ⟨sub, hs⟩ := reply c hc
        exact (spec c sub hs).2.2

-- ============================================================================
-- Section 4: (3, 4, 3) and the Refutation of the Old Projection Argument
-- ============================================================================

-- The original 132-node certificate for (3, 4, 3)
def cert_3_4_3 : WinCert :=
  WinCert.branch 1 [(0, WinCert.branch 2 [(3, WinCert.branch 5 [(4, WinCert.imm 8), (6, WinCert.imm 8), (7, WinCert.imm 8), (8, WinCert.imm 9), (9, WinCert.imm 8), (10, WinCert.imm 8), (11, WinCert.imm 8)]), (4, WinCert.imm 3), (5, WinCert.imm 3), (6, WinCert.imm 3), (7, WinCert.imm 3), (8, WinCert.imm 3), (9, WinCert.imm 3), (10, WinCert.imm 3), (11, WinCert.imm 3)]), (2, WinCert.branch 5 [(0, WinCert.imm 9), (3, WinCert.imm 9), (4, WinCert.imm 9), (6, WinCert.imm 9), (7, WinCert.imm 9), (8, WinCert.imm 9), (9, WinCert.branch 6 [(0, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4)]), (10, WinCert.imm 9), (11, WinCert.imm 9)]), (3, WinCert.branch 0 [(2, WinCert.branch 5 [(4, WinCert.imm 9), (6, WinCert.imm 9), (7, WinCert.imm 9), (8, WinCert.imm 9), (9, WinCert.imm 10), (10, WinCert.imm 9), (11, WinCert.imm 9)]), (4, WinCert.imm 2), (5, WinCert.imm 2), (6, WinCert.imm 2), (7, WinCert.imm 2), (8, WinCert.imm 2), (9, WinCert.imm 2), (10, WinCert.imm 2), (11, WinCert.imm 2)]), (4, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (5, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (6, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (7, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (8, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (9, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0)]), (10, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (11, WinCert.imm 0)]), (11, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0)])]

-- Re-checked under strong-game rules (Player 2 lines and draws now detected).
theorem win_3_4_3_certified :
    checkCert (genLines 3 4 3) Player.P1 4 (emptyBoard 12) cert_3_4_3 = true := by decide

-- Semantic consequence: Player 1 forces a win on 3 x 4 within 4 own moves (7 plies).
theorem mnk_3_4_3_first_player_win :
    ForcesWin (genLines 3 4 3) Player.P1 4 (emptyBoard 12) :=
  checkCert_sound _ _ _ _ _ win_3_4_3_certified

def embed_34_into_3n (n idx : Nat) : Nat :=
  let r := idx / 4
  let c := idx % 4
  r * n + c

theorem embed_in_bounds (n idx : Nat) (hn : 4 <= n) (hidx : idx < 12) :
    embed_34_into_3n n idx < 3 * n := by
  dsimp [embed_34_into_3n]
  have hr : idx / 4 <= 2 := by omega
  have hc : idx % 4 < n := by omega
  have hmul : (idx / 4) * n <= 2 * n := Nat.mul_le_mul_right n hr
  omega

def certMove : WinCert → List Nat → Option Nat
  | WinCert.imm m, [] => some m
  | WinCert.branch m _, [] => some m
  | WinCert.branch _ bs, c :: rs =>
      match findBranch c bs with
      | some sub => certMove sub rs
      | none => none
  | WinCert.imm _, _ :: _ => none

def play (b : Board) : List (Nat × Player) → Option Board
  | [] => some b
  | (x, pl) :: rest => if isLegalMove b x then play (setCell b x pl) rest else none

def projectedBoard_3_5 : Board :=
  setCell (setCell (setCell (setCell (setCell (emptyBoard 15) 1 .P1) 3 .P2) 0 .P1) 2 .P2) 6 .P1

/-- The former "Subgrid Monotone Projection" fails on 3 x 5: following the 3 x 4
    strategy (moves 1, 0, 5 embedded as 1, 0, 6), Player 2 answers at (0, 4) and
    completes (0,2)-(0,3)-(0,4) before Player 1's winning move. -/
theorem subgrid_projection_counterexample_3_5_3 :
    certMove cert_3_4_3 [] = some 1 ∧
    certMove cert_3_4_3 [3] = some 0 ∧
    certMove cert_3_4_3 [3, 2] = some 5 ∧
    [1, 3, 0, 2, 5].map (embed_34_into_3n 5) = [1, 3, 0, 2, 6] ∧
    play (emptyBoard 15) [(1, .P1), (3, .P2), (0, .P1), (2, .P2), (6, .P1)] = some projectedBoard_3_5 ∧
    checkWin projectedBoard_3_5 .P1 (genLines 3 5 3) = false ∧
    checkWin projectedBoard_3_5 .P2 (genLines 3 5 3) = false ∧
    isLegalMove projectedBoard_3_5 4 = true ∧
    checkWin (setCell projectedBoard_3_5 4 .P2) .P2 (genLines 3 5 3) = true := by
  decide

-- ============================================================================
-- Section 5: Independent Re-Check of the Window Certificates
-- (the lifting theorem `window_certificate_lifts` is proved in Rocq, MNKWindow.v)
-- ============================================================================

def wEdge (R C k : Nat) (rowfar colfar : Bool) (i : Nat) : Bool :=
  (rowfar && decide (R < i / C + k)) || (colfar && decide (C < i % C + k))

def edgeP2 (R C k : Nat) (rowfar colfar : Bool) (wb : Board) : Nat :=
  ((List.range (R * C)).filter (fun i => wEdge R C k rowfar colfar i && cellOwnedBy wb .P2 i)).length

def danger (R C k : Nat) (rowfar colfar : Bool) (wb : Board) (far : Nat) : Bool :=
  checkWin wb .P2 (genLines R C k) ||
  (decide (1 ≤ far) && decide (k ≤ far + edgeP2 R C k rowfar colfar wb))

mutual
  def wcheck (R C k : Nat) (rowfar colfar : Bool) : Nat → Board → Nat → WinCert → Bool
    | 0, _, _, _ => false
    | _ + 1, wb, _, WinCert.imm m =>
        isLegalMove wb m && checkWin (setCell wb m .P1) .P1 (genLines R C k)
    | d + 1, wb, far, WinCert.branch m bs =>
        isLegalMove wb m &&
        !(legalMoves (setCell wb m .P1)).isEmpty &&
        (legalMoves (setCell wb m .P1)).all (fun c => (findBranch c bs).isSome) &&
        (findBranch (R * C) bs).isSome &&
        wcheckBr R C k rowfar colfar d (setCell wb m .P1) far bs

  def wcheckBr (R C k : Nat) (rowfar colfar : Bool) (d : Nat) (wb1 : Board) (far : Nat) :
      List (Nat × WinCert) → Bool
    | [] => true
    | (c, sub) :: rest =>
        (if c == R * C then
          !(danger R C k rowfar colfar wb1 (far + 1)) &&
          wcheck R C k rowfar colfar d wb1 (far + 1) sub
        else
          isLegalMove wb1 c &&
          !(danger R C k rowfar colfar (setCell wb1 c .P2) far) &&
          wcheck R C k rowfar colfar d (setCell wb1 c .P2) far sub) &&
        wcheckBr R C k rowfar colfar d wb1 far rest
end

-- 3 x 4 window of a 3 x n board (columns >= 4 are "far"): proves (3, n, 3), n >= 4.
def cert_strip : WinCert :=
  WinCert.branch 1 [(0, WinCert.branch 2 [(3, WinCert.branch 5 [(4, WinCert.imm 8), (6, WinCert.imm 8), (7, WinCert.imm 8), (8, WinCert.imm 9), (9, WinCert.imm 8), (10, WinCert.imm 8), (11, WinCert.imm 8), (12, WinCert.imm 8)]), (4, WinCert.imm 3), (5, WinCert.imm 3), (6, WinCert.imm 3), (7, WinCert.imm 3), (8, WinCert.imm 3), (9, WinCert.imm 3), (10, WinCert.imm 3), (11, WinCert.imm 3), (12, WinCert.imm 3)]), (2, WinCert.branch 5 [(0, WinCert.imm 9), (3, WinCert.imm 9), (4, WinCert.imm 9), (6, WinCert.imm 9), (7, WinCert.imm 9), (8, WinCert.imm 9), (9, WinCert.branch 6 [(0, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4)]), (10, WinCert.imm 9), (11, WinCert.imm 9), (12, WinCert.imm 9)]), (3, WinCert.branch 2 [(0, WinCert.branch 5 [(4, WinCert.imm 8), (6, WinCert.imm 8), (7, WinCert.imm 8), (8, WinCert.imm 9), (9, WinCert.imm 8), (10, WinCert.imm 8), (11, WinCert.imm 8), (12, WinCert.imm 8)]), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (4, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (5, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (6, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (7, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (8, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (9, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (10, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (11, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (12, WinCert.imm 0)]), (12, WinCert.branch 2 [(0, WinCert.imm 3), (3, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (6, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)])]

theorem cert_strip_valid : wcheck 3 4 3 false true 4 (emptyBoard 12) 0 cert_strip = true := by
  decide

-- 4 x 3 window of an m x 3 board (rows >= 4 are "far"): proves (m, 3, 3), m >= 4.
def cert_tall : WinCert :=
  WinCert.branch 3 [(0, WinCert.branch 4 [(1, WinCert.imm 5), (2, WinCert.imm 5), (5, WinCert.branch 6 [(1, WinCert.imm 2), (2, WinCert.imm 9), (7, WinCert.imm 2), (8, WinCert.imm 2), (9, WinCert.imm 2), (10, WinCert.imm 2), (11, WinCert.imm 2), (12, WinCert.imm 2)]), (6, WinCert.imm 5), (7, WinCert.imm 5), (8, WinCert.imm 5), (9, WinCert.imm 5), (10, WinCert.imm 5), (11, WinCert.imm 5), (12, WinCert.imm 5)]), (1, WinCert.branch 6 [(0, WinCert.imm 9), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (2, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (4, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (5, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (6, WinCert.branch 4 [(0, WinCert.imm 5), (1, WinCert.imm 5), (2, WinCert.imm 5), (5, WinCert.branch 7 [(0, WinCert.imm 1), (1, WinCert.imm 10), (2, WinCert.imm 1), (8, WinCert.imm 1), (9, WinCert.imm 1), (10, WinCert.imm 1), (11, WinCert.imm 1), (12, WinCert.imm 1)]), (7, WinCert.imm 5), (8, WinCert.imm 5), (9, WinCert.imm 5), (10, WinCert.imm 5), (11, WinCert.imm 5), (12, WinCert.imm 5)]), (7, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (8, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (9, WinCert.branch 4 [(0, WinCert.imm 5), (1, WinCert.imm 5), (2, WinCert.imm 5), (5, WinCert.branch 7 [(0, WinCert.imm 1), (1, WinCert.imm 10), (2, WinCert.imm 1), (6, WinCert.imm 1), (8, WinCert.imm 1), (10, WinCert.imm 1), (11, WinCert.imm 1), (12, WinCert.imm 1)]), (6, WinCert.imm 5), (7, WinCert.imm 5), (8, WinCert.imm 5), (10, WinCert.imm 5), (11, WinCert.imm 5), (12, WinCert.imm 5)]), (10, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)]), (11, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (12, WinCert.imm 0)]), (12, WinCert.branch 6 [(0, WinCert.imm 9), (1, WinCert.imm 0), (2, WinCert.imm 0), (4, WinCert.imm 0), (5, WinCert.imm 0), (7, WinCert.imm 0), (8, WinCert.imm 0), (9, WinCert.imm 0), (10, WinCert.imm 0), (11, WinCert.imm 0), (12, WinCert.imm 0)])]

theorem cert_tall_valid : wcheck 4 3 3 true false 4 (emptyBoard 12) 0 cert_tall = true := by
  decide

-- 4 x 4 corner window of an m x n board: proves (m, n, 3) within 5 plies, m, n >= 4.
def cert_corner : WinCert :=
  WinCert.branch 5 [(0, WinCert.branch 6 [(1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (1, WinCert.branch 6 [(0, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (2, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (3, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (4, WinCert.branch 9 [(0, WinCert.imm 1), (1, WinCert.imm 13), (2, WinCert.imm 1), (3, WinCert.imm 1), (6, WinCert.imm 1), (7, WinCert.imm 1), (8, WinCert.imm 1), (10, WinCert.imm 1), (11, WinCert.imm 1), (12, WinCert.imm 1), (13, WinCert.imm 1), (14, WinCert.imm 1), (15, WinCert.imm 1), (16, WinCert.imm 1)]), (6, WinCert.branch 9 [(0, WinCert.imm 1), (1, WinCert.imm 13), (2, WinCert.imm 1), (3, WinCert.imm 1), (4, WinCert.imm 1), (7, WinCert.imm 1), (8, WinCert.imm 1), (10, WinCert.imm 1), (11, WinCert.imm 1), (12, WinCert.imm 1), (13, WinCert.imm 1), (14, WinCert.imm 1), (15, WinCert.imm 1), (16, WinCert.imm 1)]), (7, WinCert.branch 9 [(0, WinCert.imm 1), (1, WinCert.imm 13), (2, WinCert.imm 1), (3, WinCert.imm 1), (4, WinCert.imm 1), (6, WinCert.imm 1), (8, WinCert.imm 1), (10, WinCert.imm 1), (11, WinCert.imm 1), (12, WinCert.imm 1), (13, WinCert.imm 1), (14, WinCert.imm 1), (15, WinCert.imm 1), (16, WinCert.imm 1)]), (8, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (9, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (10, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (11, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (12, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (13, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (14, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)]), (15, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (16, WinCert.imm 4)]), (16, WinCert.branch 6 [(0, WinCert.imm 4), (1, WinCert.imm 4), (2, WinCert.imm 4), (3, WinCert.imm 4), (4, WinCert.imm 7), (7, WinCert.imm 4), (8, WinCert.imm 4), (9, WinCert.imm 4), (10, WinCert.imm 4), (11, WinCert.imm 4), (12, WinCert.imm 4), (13, WinCert.imm 4), (14, WinCert.imm 4), (15, WinCert.imm 4), (16, WinCert.imm 4)])]

theorem cert_corner_valid : wcheck 4 4 3 true true 3 (emptyBoard 16) 0 cert_corner = true := by
  decide

-- Strict Axiom Validation
#print axioms otherPlayer_involutive
#print axioms mnk_3_3_3_lines
#print axioms mnk_3_4_3_lines
#print axioms mnk_4_4_4_lines
#print axioms mnk_5_4_4_lines
#print axioms mnk_6_4_4_lines
#print axioms mnk_7_4_4_lines
#print axioms mnk_8_4_4_lines
#print axioms mnk_5_5_4_lines
#print axioms mnk_8_8_5_lines
#print axioms mnk_15_15_5_lines
#print axioms genLines_count_3_3_3
#print axioms genLines_count_3_4_3
#print axioms genLines_count_5_4_4
#print axioms genLines_count_8_8_5
#print axioms mnk_prime_triple_7_5_3_lines
#print axioms mnk_prime_triple_11_7_5_lines
#print axioms mnk_prime_triple_13_11_7_lines
#print axioms mnk_prime_triple_11_7_7_lines
#print axioms mnk_prime_triple_17_13_11_lines
#print axioms mnk_prime_triple_19_17_13_lines
#print axioms mnk_prime_triple_11_7_7_erdos_bound
#print axioms mnk_prime_triple_17_13_11_erdos_bound
#print axioms mnk_prime_triple_19_17_13_erdos_bound
#print axioms lines_3_3_3_count
#print axioms lines_3_4_3_count
#print axioms lines_3_4_3_generated
#print axioms mem_legalMoves
#print axioms findBranch_mem
#print axioms checkBranches_spec
#print axioms checkCert_sound
#print axioms win_3_4_3_certified
#print axioms mnk_3_4_3_first_player_win
#print axioms embed_in_bounds
#print axioms subgrid_projection_counterexample_3_5_3
#print axioms cert_strip_valid
#print axioms cert_tall_valid
#print axioms cert_corner_valid
