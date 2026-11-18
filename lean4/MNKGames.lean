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
6. The Erdős–Selfridge theorem (Maker–Breaker, Breaker second or first, for
   arbitrary hypergraphs) and its strong-game corollary `erdos_selfridge_draw`,
   giving formal draws of (11,7,7), (17,13,11) and (19,17,13), and the refined
   version erdos_selfridge_draw_refined, which settles (4,4,4).
7. Strategy stealing: on every hypergraph the second player never forces a win
   (`strategy_stealing`).

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

-- ============================================================================
-- Section 6: The Erdős–Selfridge Theorem (independent re-proof)
-- Potential-function argument with weights scaled by 2^K (see MNKErdosSelfridge.v).
-- ============================================================================

/-- Maker–Breaker semantics: Maker `p` claims a whole line within `d` own moves
    against every Breaker reply; Breaker's lines are irrelevant. -/
inductive MakerWins (lines : List (List Nat)) (p : Player) : Nat → Board → Prop where
  | now (d : Nat) (b : Board) (m : Nat) :
      isLegalMove b m = true →
      checkWin (setCell b m p) p lines = true →
      MakerWins lines p (d + 1) b
  | next (d : Nat) (b : Board) (m : Nat) :
      isLegalMove b m = true →
      (∃ c, isLegalMove (setCell b m p) c = true) →
      (∀ c, isLegalMove (setCell b m p) c = true →
        MakerWins lines p d (setCell (setCell b m p) c (otherPlayer p))) →
      MakerWins lines p (d + 1) b

theorem forcesWin_makerWins {lines : List (List Nat)} {p : Player} {d : Nat} {b : Board}
    (h : ForcesWin lines p d b) : MakerWins lines p d b := by
  induction h with
  | now d b m hm hw => exact MakerWins.now d b m hm hw
  | next d b m hm hex _ _ ih => exact MakerWins.next d b m hm hex ih

theorem setCell_eq_set : ∀ (b : Board) (i : Nat) (p : Player), setCell b i p = b.set i (some p)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | hd :: tl, i + 1, p => by simp [setCell, setCell_eq_set tl i p]

theorem getCell_eq (b : Board) (j : Nat) : getCell b j = (b[j]?).getD none := by
  simp [getCell, List.getD_eq_getElem?_getD]

theorem setCell_length' (b : Board) (i : Nat) (p : Player) : (setCell b i p).length = b.length := by
  simp [setCell_eq_set]

theorem getCell_setCell (b : Board) (i j : Nat) (r : Player) (hi : i < b.length) :
    getCell (setCell b i r) j = if j = i then some r else getCell b j := by
  rw [getCell_eq, getCell_eq, setCell_eq_set, List.getElem?_set]
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

theorem isLegalMove_iff (b : Board) (x : Nat) :
    isLegalMove b x = true ↔ x < b.length ∧ getCell b x = none := by
  unfold isLegalMove isCellEmpty
  cases hc : getCell b x <;> simp

theorem checkWin_iff (b : Board) (p : Player) (lines : List (List Nat)) :
    checkWin b p lines = true ↔ ∃ L, L ∈ lines ∧ ∀ y, y ∈ L → getCell b y = some p := by
  unfold checkWin lineOwnedBy cellOwnedBy
  simp only [List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨L, hL, h⟩
    refine ⟨L, hL, fun y hy => ?_⟩
    have := h y hy
    cases hc : getCell b y with
    | none => rw [hc] at this; simp at this
    | some q => rw [hc] at this; simp at this; rw [this]
  · rintro ⟨L, hL, h⟩
    exact ⟨L, hL, fun y hy => by rw [h y hy]; simp⟩

theorem cellOwnedBy_setCell (b : Board) (x : Nat) (r s : Player) (y : Nat) (hx : x < b.length) :
    cellOwnedBy (setCell b x r) s y = if y = x then (r == s) else cellOwnedBy b s y := by
  unfold cellOwnedBy
  rw [getCell_setCell b x y r hx]
  by_cases h : y = x <;> simp [h]

theorem cellOwnedBy_none (b : Board) (s : Player) (x : Nat) (h : getCell b x = none) :
    cellOwnedBy b s x = false := by
  unfold cellOwnedBy; rw [h]

theorem otherPlayer_ne (p : Player) : (otherPlayer p == p) = false := by cases p <;> rfl
theorem player_beq_self (p : Player) : (p == p) = true := by cases p <;> rfl

theorem sum_map_add (l : List (List Nat)) (f g : List Nat → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sum_map_le (l : List (List Nat)) (f g : List Nat → Nat) (h : ∀ x, x ∈ l → f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

theorem sum_map_congr (l : List (List Nat)) (f g : List Nat → Nat) (h : ∀ x, x ∈ l → f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem le_sum_map (l : List (List Nat)) (f : List Nat → Nat) (a : List Nat) (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with h | h
    · subst h; omega
    · have := ih h; omega

theorem all_congr_mem {f g : Nat → Bool} : ∀ (l : List Nat), (∀ y, y ∈ l → f y = g y) →
    l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.all_cons, h a List.mem_cons_self,
        all_congr_mem l (fun y hy => h y (List.mem_cons_of_mem a hy))]

theorem filter_congr_mem {f g : Nat → Bool} : ∀ (l : List Nat), (∀ y, y ∈ l → f y = g y) →
    l.filter f = l.filter g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filter_cons, List.filter_cons, h a List.mem_cons_self,
        filter_congr_mem l (fun y hy => h y (List.mem_cons_of_mem a hy))]

theorem filter_all_true {f : Nat → Bool} : ∀ (l : List Nat), (∀ y, y ∈ l → f y = true) →
    l.filter f = l
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filter_cons, ite_eq_left (h a List.mem_cons_self),
        filter_all_true l (fun y hy => h y (List.mem_cons_of_mem a hy))]

theorem filter_all_false {f : Nat → Bool} : ∀ (l : List Nat), (∀ y, y ∈ l → f y = false) →
    l.filter f = []
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filter_cons, ite_eq_right (by simp [h a List.mem_cons_self]),
        filter_all_false l (fun y hy => h y (List.mem_cons_of_mem a hy))]

theorem getCell_emptyBoard (N y : Nat) : getCell (emptyBoard N) y = none := by
  rw [getCell_eq]; unfold emptyBoard; rw [List.getElem?_replicate]; split <;> rfl

/-- A line is alive for Maker `p` when Breaker owns none of its cells. -/
def alive (b : Board) (p : Player) (L : List Nat) : Bool :=
  L.all (fun x => !cellOwnedBy b (otherPlayer p) x)

def owned (b : Board) (p : Player) (L : List Nat) : Nat :=
  (L.filter (cellOwnedBy b p)).length

/-- Scaled weight 2^K * 2^(-(cells still to claim)) of a live line. -/
def lw (K : Nat) (b : Board) (p : Player) (L : List Nat) : Nat :=
  if alive b p L then 2 ^ (K - L.length + owned b p L) else 0

def phi (K : Nat) (b : Board) (p : Player) (lines : List (List Nat)) : Nat :=
  (lines.map (lw K b p)).sum

def wgt (K : Nat) (b : Board) (p : Player) (lines : List (List Nat)) (x : Nat) : Nat :=
  (lines.map (fun L => if x ∈ L then lw K b p L else 0)).sum

theorem alive_maker (b : Board) (x : Nat) (p : Player) (L : List Nat)
    (hx : isLegalMove b x = true) : alive (setCell b x p) p L = alive b p L := by
  obtain ⟨hlt, he⟩ := (isLegalMove_iff b x).mp hx
  unfold alive
  congr 1
  funext y
  rw [cellOwnedBy_setCell b x p (otherPlayer p) y hlt]
  by_cases h : y = x
  · rw [ite_eq_left h, h, cellOwnedBy_none b _ x he]; cases p <;> rfl
  · rw [ite_eq_right h]

theorem owned_maker (b : Board) (x : Nat) (p : Player) (hx : isLegalMove b x = true) :
    ∀ (L : List Nat), L.Nodup →
      owned (setCell b x p) p L = owned b p L + (if x ∈ L then 1 else 0) := by
  obtain ⟨hlt, he⟩ := (isLegalMove_iff b x).mp hx
  intro L
  induction L with
  | nil => intro _; simp [owned]
  | cons a l ih =>
    intro hnd
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have ih' := ih hnd'
    unfold owned at ih' ⊢
    rw [List.filter_cons, List.filter_cons, cellOwnedBy_setCell b x p p a hlt]
    by_cases h : a = x
    · have hcx : cellOwnedBy b p a = false := by rw [h]; exact cellOwnedBy_none b p x he
      have hxl : x ∉ l := by rw [← h]; exact hnot
      have hxm : x ∈ a :: l := by rw [h]; exact List.mem_cons_self
      rw [ite_eq_left h, player_beq_self, ite_eq_left rfl, hcx, ite_eq_left hxm,
        ite_eq_right (by decide : ¬ (false = true)), List.length_cons]
      rw [ite_eq_right hxl] at ih'
      omega
    · have hxm : (x ∈ a :: l) ↔ x ∈ l := by simp [List.mem_cons, Ne.symm h]
      rw [ite_eq_right h]
      by_cases hc : cellOwnedBy b p a = true
      · rw [ite_eq_left hc, ite_eq_left hc, List.length_cons, List.length_cons]
        by_cases hm : x ∈ l
        · rw [ite_eq_left (hxm.mpr hm)]; rw [ite_eq_left hm] at ih'; omega
        · rw [ite_eq_right (fun e => hm (hxm.mp e))]; rw [ite_eq_right hm] at ih'; omega
      · rw [ite_eq_right hc, ite_eq_right hc]
        by_cases hm : x ∈ l
        · rw [ite_eq_left (hxm.mpr hm)]; rw [ite_eq_left hm] at ih'; omega
        · rw [ite_eq_right (fun e => hm (hxm.mp e))]; rw [ite_eq_right hm] at ih'; omega

theorem lw_maker (K : Nat) (b : Board) (x : Nat) (p : Player) (L : List Nat)
    (hx : isLegalMove b x = true) (hnd : L.Nodup) :
    lw K (setCell b x p) p L = lw K b p L + (if x ∈ L then lw K b p L else 0) := by
  unfold lw
  rw [alive_maker b x p L hx, owned_maker b x p hx L hnd]
  by_cases ha : alive b p L = true
  · by_cases hm : x ∈ L
    · have key : ∀ e : Nat, 2 ^ (e + 1) = 2 ^ e + 2 ^ e := fun e => by rw [Nat.pow_succ]; omega
      simp [ha, hm, ← Nat.add_assoc, key]
    · simp [ha, hm]
  · simp [ha]

theorem lw_breaker (K : Nat) (b : Board) (x : Nat) (p : Player) (L : List Nat)
    (hx : isLegalMove b x = true) :
    lw K (setCell b x (otherPlayer p)) p L = if x ∈ L then 0 else lw K b p L := by
  obtain ⟨hlt, he⟩ := (isLegalMove_iff b x).mp hx
  by_cases hm : x ∈ L
  · have hdead : alive (setCell b x (otherPlayer p)) p L = false := by
      cases hc : alive (setCell b x (otherPlayer p)) p L
      · rfl
      · exfalso
        unfold alive at hc
        have := (List.all_eq_true.mp hc) x hm
        try dsimp only at this
        rw [cellOwnedBy_setCell b x _ _ x hlt, ite_eq_left rfl, player_beq_self] at this
        exact absurd this (by decide)
    simp [lw, hdead, hm]
  · have hal : alive (setCell b x (otherPlayer p)) p L = alive b p L := by
      unfold alive
      apply all_congr_mem
      intro y hy
      have hyx : y ≠ x := fun e => hm (e ▸ hy)
      try dsimp only
      rw [cellOwnedBy_setCell b x _ _ y hlt, ite_eq_right hyx]
    have how : owned (setCell b x (otherPlayer p)) p L = owned b p L := by
      unfold owned
      rw [filter_congr_mem L (fun y hy => by
        have hyx : y ≠ x := fun e => hm (e ▸ hy)
        rw [cellOwnedBy_setCell b x _ _ y hlt, ite_eq_right hyx])]
    simp [lw, hal, how, hm]

theorem phi_maker (K : Nat) (b : Board) (x : Nat) (p : Player) (lines : List (List Nat))
    (hnd : ∀ L, L ∈ lines → L.Nodup) (hx : isLegalMove b x = true) :
    phi K (setCell b x p) p lines = phi K b p lines + wgt K b p lines x := by
  unfold phi wgt
  rw [← sum_map_add]
  exact sum_map_congr _ _ _ (fun L hL => lw_maker K b x p L hx (hnd L hL))

theorem phi_breaker (K : Nat) (b : Board) (x : Nat) (p : Player) (lines : List (List Nat))
    (hx : isLegalMove b x = true) :
    phi K (setCell b x (otherPlayer p)) p lines + wgt K b p lines x = phi K b p lines := by
  unfold phi wgt
  rw [← sum_map_add]
  apply sum_map_congr
  intro L _
  show lw K (setCell b x (otherPlayer p)) p L + (if x ∈ L then lw K b p L else 0) = lw K b p L
  rw [lw_breaker K b x p L hx]
  by_cases hm : x ∈ L <;> simp [hm]

theorem wgt_breaker_le (K : Nat) (b : Board) (x : Nat) (p : Player) (lines : List (List Nat))
    (y : Nat) (hx : isLegalMove b x = true) :
    wgt K (setCell b x (otherPlayer p)) p lines y ≤ wgt K b p lines y := by
  unfold wgt
  apply sum_map_le
  intro L _
  show (if y ∈ L then lw K (setCell b x (otherPlayer p)) p L else 0) ≤ (if y ∈ L then lw K b p L else 0)
  rw [lw_breaker K b x p L hx]
  by_cases hy : y ∈ L <;> by_cases hx' : x ∈ L <;> simp [hy, hx']

theorem wgt_le_phi (K : Nat) (b : Board) (p : Player) (lines : List (List Nat)) (x : Nat) :
    wgt K b p lines x ≤ phi K b p lines := by
  unfold wgt phi
  apply sum_map_le
  intro L _
  show (if x ∈ L then lw K b p L else 0) ≤ lw K b p L
  by_cases h : x ∈ L <;> simp [h]

theorem phi_full (K : Nat) (b : Board) (p : Player) (lines : List (List Nat)) (L : List Nat)
    (hL : L ∈ lines) (hK : L.length ≤ K) (hown : ∀ y, y ∈ L → getCell b y = some p) :
    2 ^ K ≤ phi K b p lines := by
  have ha : alive b p L = true := by
    unfold alive
    apply List.all_eq_true.mpr
    intro y hy
    try dsimp only
    unfold cellOwnedBy; rw [hown y hy]; cases p <;> rfl
  have ho : owned b p L = L.length := by
    unfold owned
    rw [filter_all_true L (fun y hy => by unfold cellOwnedBy; rw [hown y hy]; cases p <;> rfl)]
  have hw : lw K b p L = 2 ^ K := by
    unfold lw; rw [ite_eq_left ha, ho]
    congr 1; omega
  have := le_sum_map lines (lw K b p) L hL
  unfold phi; omega

theorem legal_after_set (b : Board) (c : Nat) (r : Player) (y : Nat)
    (hc : isLegalMove b c = true) (hy : isLegalMove (setCell b c r) y = true) :
    isLegalMove b y = true ∧ y ≠ c := by
  obtain ⟨hclt, _⟩ := (isLegalMove_iff b c).mp hc
  obtain ⟨hylt, hye⟩ := (isLegalMove_iff _ y).mp hy
  rw [setCell_length'] at hylt
  rw [getCell_setCell b c y r hclt] at hye
  by_cases h : y = c
  · simp [h] at hye
  · simp [h] at hye
    exact ⟨(isLegalMove_iff b y).mpr ⟨hylt, hye⟩, h⟩

theorem argmax_in (f : Nat → Nat) : ∀ (l : List Nat), l ≠ [] →
    ∃ c, c ∈ l ∧ ∀ y, y ∈ l → f y ≤ f c
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by
      simp at hy; subst hy; exact Nat.le_refl _⟩
  | a :: a' :: l, _ => by
      obtain ⟨c, hc, hmax⟩ := argmax_in f (a' :: l) (by simp)
      by_cases h : f a ≤ f c
      · refine ⟨c, List.mem_cons_of_mem a hc, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with e | e
        · rw [e]; exact h
        · exact hmax y e
      · refine ⟨a, List.mem_cons_self, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with e | e
        · rw [e]; exact Nat.le_refl _
        · have := hmax y e; omega

section ErdosSelfridge

variable (lines : List (List Nat)) (K : Nat)

/-- `esSum` = 2^K * Σ_L 2^(-|L|). -/
def esSum : Nat := (lines.map (fun L => 2 ^ (K - L.length))).sum

theorem phi_empty (N : Nat) (p : Player) : phi K (emptyBoard N) p lines = esSum lines K := by
  unfold phi esSum
  apply sum_map_congr
  intro L _
  have ha : alive (emptyBoard N) p L = true := by
    unfold alive
    apply List.all_eq_true.mpr
    intro y _
    try dsimp only
    rw [cellOwnedBy_none _ _ y (getCell_emptyBoard N y)]
    rfl
  have ho : owned (emptyBoard N) p L = 0 := by
    unfold owned
    rw [filter_all_false L (fun y _ => cellOwnedBy_none _ _ y (getCell_emptyBoard N y))]
    rfl
  unfold lw; rw [ite_eq_left ha, ho, Nat.add_zero]

def esInv (p : Player) (b : Board) : Prop :=
  ∀ x, isLegalMove b x = true → phi K b p lines + wgt K b p lines x < 2 ^ K

theorem breaker_choice (p : Player) (b : Board) (h : ∃ c, isLegalMove b c = true) :
    ∃ c, isLegalMove b c = true ∧
      ∀ y, isLegalMove b y = true → wgt K b p lines y ≤ wgt K b p lines c := by
  obtain ⟨c0, hc0⟩ := h
  have hne : legalMoves b ≠ [] := by
    intro e; have := mem_legalMoves.mpr hc0; rw [e] at this; simp at this
  obtain ⟨c, hc, hmax⟩ := argmax_in (wgt K b p lines) (legalMoves b) hne
  exact ⟨c, mem_legalMoves.mp hc, fun y hy => hmax y (mem_legalMoves.mpr hy)⟩

theorem breaker_reply_bound (p : Player) (b : Board) (c : Nat)
    (hc : isLegalMove b c = true)
    (hmax : ∀ y, isLegalMove b y = true → wgt K b p lines y ≤ wgt K b p lines c)
    (y : Nat) (hy : isLegalMove (setCell b c (otherPlayer p)) y = true) :
    phi K (setCell b c (otherPlayer p)) p lines + wgt K (setCell b c (otherPlayer p)) p lines y
      ≤ phi K b p lines := by
  have e := phi_breaker K b c p lines hc
  have hle := wgt_breaker_le K b c p lines y hc
  have hm := hmax y (legal_after_set b c _ y hc hy).1
  omega

variable (hlines : ∀ L, L ∈ lines → L.Nodup ∧ L.length ≤ K)
include hlines

theorem erdos_selfridge_potential (p : Player) (d : Nat) (b : Board)
    (hinv : esInv lines K p b) : ¬ MakerWins lines p d b := by
  intro h
  revert hinv
  induction h with
  | now d b m hm hw =>
    intro hinv
    obtain ⟨L, hL, hown⟩ := (checkWin_iff _ _ _).mp hw
    have hlt := hinv m hm
    rw [← phi_maker K b m p lines (fun L hL => (hlines L hL).1) hm] at hlt
    have hge := phi_full K (setCell b m p) p lines L hL (hlines L hL).2 hown
    omega
  | next d b m hm hex _ ih =>
    intro hinv
    obtain ⟨c, hc, hmax⟩ := breaker_choice lines K p (setCell b m p) hex
    apply ih c hc
    unfold esInv
    intro y hy
    have hb := breaker_reply_bound lines K p (setCell b m p) c hc hmax y hy
    have hlt := hinv m hm
    rw [← phi_maker K b m p lines (fun L hL => (hlines L hL).1) hm] at hlt
    omega

/-- Erdős–Selfridge, Breaker second: Σ 2^(-|L|) < 1/2 ⇒ Maker never claims a line. -/
theorem erdos_selfridge_breaker_second (N : Nat) (p : Player) (h : 2 * esSum lines K < 2 ^ K)
    (d : Nat) : ¬ MakerWins lines p d (emptyBoard N) := by
  apply erdos_selfridge_potential lines K hlines
  unfold esInv
  intro x _
  have hw := wgt_le_phi K (emptyBoard N) p lines x
  rw [phi_empty] at hw ⊢
  omega

/-- Erdős–Selfridge, Breaker `p` first: Σ 2^(-|L|) < 1 ⇒ after a greedy opening,
    Maker never claims a line. -/
theorem erdos_selfridge_breaker_first (N : Nat) (p : Player) (hN : 0 < N)
    (h : esSum lines K < 2 ^ K) :
    ∃ m, isLegalMove (emptyBoard N) m = true ∧
      ∀ d, ¬ MakerWins lines (otherPlayer p) d (setCell (emptyBoard N) m p) := by
  have h0 : ∃ c, isLegalMove (emptyBoard N) c = true :=
    ⟨0, (isLegalMove_iff _ 0).mpr ⟨by simp [emptyBoard]; omega, getCell_emptyBoard N 0⟩⟩
  obtain ⟨m, hm, hmax⟩ := breaker_choice lines K (otherPlayer p) (emptyBoard N) h0
  refine ⟨m, hm, fun d => ?_⟩
  apply erdos_selfridge_potential lines K hlines
  unfold esInv
  intro y hy
  have hb := breaker_reply_bound lines K (otherPlayer p) (emptyBoard N) m hm hmax y
  rw [otherPlayer_involutive, phi_empty] at hb
  have := hb hy
  omega

end ErdosSelfridge

def SecondForcesWin (lines : List (List Nat)) (d : Nat) (b : Board) : Prop :=
  (∃ m, isLegalMove b m = true) ∧
  ∀ m, isLegalMove b m = true →
    checkWin (setCell b m .P1) .P1 lines = false ∧ ForcesWin lines .P2 d (setCell b m .P1)

def GameIsDraw (lines : List (List Nat)) (b : Board) : Prop :=
  (∀ d, ¬ ForcesWin lines .P1 d b) ∧ (∀ d, ¬ SecondForcesWin lines d b)

/-- Strong-game corollary: Σ 2^(-|L|) < 1/2 makes the game a draw. -/
theorem erdos_selfridge_draw (lines : List (List Nat)) (K : Nat)
    (hlines : ∀ L, L ∈ lines → L.Nodup ∧ L.length ≤ K) (N : Nat)
    (h : 2 * esSum lines K < 2 ^ K) : GameIsDraw lines (emptyBoard N) := by
  refine ⟨fun d hf => erdos_selfridge_breaker_second lines K hlines N .P1 h d
    (forcesWin_makerWins hf), ?_⟩
  rintro d ⟨⟨m0, hm0⟩, hall⟩
  have hN : 0 < N := by
    have := ((isLegalMove_iff _ m0).mp hm0).1
    simp [emptyBoard] at this; omega
  obtain ⟨m, hm, hno⟩ := erdos_selfridge_breaker_first lines K hlines N .P1 hN (by omega)
  exact hno d (forcesWin_makerWins (hall m hm).2)

-- The three prime-dimension draws, now fully formal (generator facts by `decide`).
theorem mnk_prime_triple_11_7_7_draw : GameIsDraw (genLines 11 7 7) (emptyBoard (11 * 7)) :=
  erdos_selfridge_draw _ 7 (by decide) _ (by decide)

theorem mnk_prime_triple_17_13_11_draw : GameIsDraw (genLines 17 13 11) (emptyBoard (17 * 13)) :=
  erdos_selfridge_draw _ 11 (by decide +kernel) _ (by decide +kernel)

theorem mnk_prime_triple_19_17_13_draw : GameIsDraw (genLines 19 17 13) (emptyBoard (19 * 17)) :=
  erdos_selfridge_draw _ 13 (by decide +kernel) _ (by decide +kernel)

/-- Refined strong-game draw: the potential invariant itself on the empty board
    (Σ + wgt(x) < 2^K for every cell, Player 2 as Breaker moving second), plus
    Σ < 2^K (Player 1 as Breaker moving first). -/
theorem erdos_selfridge_draw_refined (lines : List (List Nat)) (K : Nat)
    (hlines : ∀ L, L ∈ lines → L.Nodup ∧ L.length ≤ K) (N : Nat)
    (hinv : ∀ x, x < N → esSum lines K + wgt K (emptyBoard N) .P1 lines x < 2 ^ K)
    (h : esSum lines K < 2 ^ K) : GameIsDraw lines (emptyBoard N) := by
  have hes : esInv lines K .P1 (emptyBoard N) := by
    unfold esInv
    intro x hx
    rw [phi_empty]
    apply hinv
    have := ((isLegalMove_iff _ x).mp hx).1
    simpa [emptyBoard] using this
  refine ⟨fun d hf => erdos_selfridge_potential lines K hlines .P1 d (emptyBoard N) hes
    (forcesWin_makerWins hf), ?_⟩
  rintro d ⟨⟨m0, hm0⟩, hall⟩
  have hN : 0 < N := by
    have := ((isLegalMove_iff _ m0).mp hm0).1
    simp [emptyBoard] at this; omega
  obtain ⟨m, hm, hno⟩ := erdos_selfridge_breaker_first lines K hlines N .P1 hN h
  exact hno d (forcesWin_makerWins (hall m hm).2)

/-- (4, 4, 4) is a draw: Σ = 10 and no cell lies on more than 3 lines, so
    10 + 3 = 13 < 16 = 2^4, although the crude test 2 · 10 < 16 fails. -/
theorem mnk_4_4_4_draw : GameIsDraw (genLines 4 4 4) (emptyBoard (4 * 4)) :=
  erdos_selfridge_draw_refined _ 4 (by decide) _ (by decide +kernel) (by decide)

-- ============================================================================
-- Section 7: Strategy Stealing (independent re-proof)
-- The second player never forces a win, on any hypergraph (see MNKStrategyStealing.v).
-- ============================================================================

theorem neq_other (p : Player) : p ≠ otherPlayer p := by cases p <;> decide
theorem other_neq (p : Player) : otherPlayer p ≠ p := by cases p <;> decide

theorem getCell_setCell_ne (b : Board) (i j : Nat) (r : Player) (h : j ≠ i) :
    getCell (setCell b i r) j = getCell b j := by
  rw [getCell_eq, getCell_eq, setCell_eq_set, List.getElem?_set, ite_eq_right (Ne.symm h)]

theorem getCell_some_lt (b : Board) (i : Nat) (p : Player) (h : getCell b i = some p) :
    i < b.length := by
  by_cases hc : i < b.length
  · exact hc
  · rw [getCell_eq, List.getElem?_eq_none (by omega)] at h
    simp at h

theorem checkWin_extra (b : Board) (x : Nat) (p : Player) (lines : List (List Nat))
    (h : checkWin b p lines = true) : checkWin (setCell b x p) p lines = true := by
  obtain ⟨L, hL, hown⟩ := (checkWin_iff _ _ _).mp h
  refine (checkWin_iff _ _ _).mpr ⟨L, hL, fun y hy => ?_⟩
  by_cases hyx : y = x
  · rw [hyx] at hy ⊢
    rw [getCell_setCell b x x p (getCell_some_lt b x p (hown x hy)), ite_eq_left rfl]
  · rw [getCell_setCell_ne b x y p hyx]; exact hown y hy

theorem setCell_comm : ∀ (b : Board) (i j : Nat) (p q : Player), i ≠ j →
    setCell (setCell b i p) j q = setCell (setCell b j q) i p
  | [], _, _, _, _, _ => rfl
  | _ :: _, 0, 0, _, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | a :: tl, i + 1, j + 1, p, q, h => by
      show a :: setCell (setCell tl i p) j q = a :: setCell (setCell tl j q) i p
      rw [setCell_comm tl i j p q (fun e => h (by rw [e]))]

theorem legal_set_other (b : Board) (y x : Nat) (r : Player)
    (hy : isLegalMove b y = true) (hne : y ≠ x) : isLegalMove (setCell b x r) y = true := by
  obtain ⟨hlt, he⟩ := (isLegalMove_iff b y).mp hy
  exact (isLegalMove_iff _ y).mpr
    ⟨by rw [setCell_length']; exact hlt, by rw [getCell_setCell_ne b x y r hne]; exact he⟩

theorem needsMove {lines : List (List Nat)} {p : Player} {d : Nat} {b : Board}
    (h : ForcesWin lines p d b) : ∃ m, isLegalMove b m = true := by
  cases h with
  | now _ _ m hm _ => exact ⟨m, hm⟩
  | next _ _ m hm _ _ _ => exact ⟨m, hm⟩

/-- A stone of one player is irrelevant to the other player's lines. -/
theorem checkWin_other_stone (b : Board) (x : Nat) (p q : Player) (lines : List (List Nat))
    (hpq : p ≠ q) (hx : isLegalMove b x = true) :
    checkWin (setCell b x p) q lines = checkWin b q lines := by
  obtain ⟨hlt, he⟩ := (isLegalMove_iff b x).mp hx
  have hf : cellOwnedBy (setCell b x p) q = cellOwnedBy b q := by
    funext y
    rw [cellOwnedBy_setCell b x p q y hlt]
    by_cases h : y = x
    · rw [ite_eq_left h, h, cellOwnedBy_none b q x he]
      cases p <;> cases q <;> first | rfl | exact absurd rfl hpq
    · rw [ite_eq_right h]
  unfold checkWin lineOwnedBy
  rw [hf]

def swapBoard (b : Board) : Board := b.map (Option.map otherPlayer)

theorem swap_length (b : Board) : (swapBoard b).length = b.length := by simp [swapBoard]

theorem swap_get (b : Board) (x : Nat) :
    getCell (swapBoard b) x = (getCell b x).map otherPlayer := by
  rw [getCell_eq, getCell_eq]; unfold swapBoard; rw [List.getElem?_map]
  cases h : b[x]? <;> rfl

theorem legal_swap (b : Board) (x : Nat) : isLegalMove (swapBoard b) x = isLegalMove b x := by
  unfold isLegalMove isCellEmpty
  rw [swap_length, swap_get]
  cases getCell b x <;> rfl

theorem swap_setCell : ∀ (b : Board) (x : Nat) (p : Player),
    setCell (swapBoard b) x (otherPlayer p) = swapBoard (setCell b x p)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: tl, x + 1, p => by
      show (Option.map otherPlayer a) :: setCell (swapBoard tl) x (otherPlayer p)
        = (Option.map otherPlayer a) :: swapBoard (setCell tl x p)
      rw [swap_setCell tl x p]

theorem owned_swap (b : Board) (p : Player) (x : Nat) :
    cellOwnedBy (swapBoard b) (otherPlayer p) x = cellOwnedBy b p x := by
  unfold cellOwnedBy
  rw [swap_get]
  cases getCell b x with
  | none => rfl
  | some q => cases p <;> cases q <;> rfl

theorem checkWin_swap (b : Board) (p : Player) (lines : List (List Nat)) :
    checkWin (swapBoard b) (otherPlayer p) lines = checkWin b p lines := by
  have hf : cellOwnedBy (swapBoard b) (otherPlayer p) = cellOwnedBy b p := funext (owned_swap b p)
  unfold checkWin lineOwnedBy
  rw [hf]

theorem swap_empty (N : Nat) : swapBoard (emptyBoard N) = emptyBoard N := by
  unfold swapBoard emptyBoard; simp [List.map_replicate]

theorem forcesWin_swap {lines : List (List Nat)} {p : Player} {d : Nat} {b : Board}
    (h : ForcesWin lines p d b) : ForcesWin lines (otherPlayer p) d (swapBoard b) := by
  induction h with
  | now d b m hm hw =>
    apply ForcesWin.now d _ m
    · rw [legal_swap]; exact hm
    · rw [swap_setCell, checkWin_swap]; exact hw
  | next d b m hm hex hno _ ih =>
    apply ForcesWin.next d _ m
    · rw [legal_swap]; exact hm
    · obtain ⟨c, hc⟩ := hex
      exact ⟨c, by rw [swap_setCell, legal_swap]; exact hc⟩
    · intro c hc
      rw [swap_setCell] at hc ⊢
      rw [legal_swap] at hc
      rw [swap_setCell, checkWin_swap]
      exact hno c hc
    · intro c hc
      rw [swap_setCell] at hc ⊢
      rw [legal_swap] at hc
      rw [swap_setCell]
      exact ih c hc

/-- An extra stone of your own colour never hurts. -/
theorem steal {lines : List (List Nat)} {p : Player} {d : Nat} {b : Board}
    (h : ForcesWin lines p d b) : ∀ x, isLegalMove b x = true →
      checkWin (setCell b x p) p lines = true ∨ ForcesWin lines p d (setCell b x p) := by
  induction h with
  | now d b m hm hw =>
    intro x hx
    by_cases hmx : m = x
    · rw [← hmx]; exact Or.inl hw
    · right
      apply ForcesWin.now d _ m (legal_set_other b m x p hm hmx)
      rw [setCell_comm b x m p p (Ne.symm hmx)]
      exact checkWin_extra _ x p lines hw
  | next d b m hm hex hno hfw ih =>
    intro x hx
    right
    by_cases hmx : m = x
    · -- the strategy asks for the cell we already own: play a free cell z instead
      rw [← hmx]
      obtain ⟨z, hz⟩ := hex
      cases ew : checkWin (setCell (setCell b m p) z p) p lines with
      | true => exact ForcesWin.now d _ z hz ew
      | false =>
        apply ForcesWin.next d _ z hz
        · obtain ⟨c, hc⟩ := needsMove (hfw z hz)
          obtain ⟨hc1, hcz⟩ := legal_after_set _ _ _ _ hz hc
          exact ⟨c, legal_set_other _ c z p hc1 hcz⟩
        · intro c hc
          obtain ⟨hc1, hcz⟩ := legal_after_set _ _ _ _ hz hc
          rw [setCell_comm (setCell b m p) z c p (otherPlayer p) (Ne.symm hcz),
            checkWin_other_stone _ z p (otherPlayer p) lines (neq_other p)
              (legal_set_other _ z c _ hz (Ne.symm hcz))]
          exact hno c hc1
        · intro c hc
          obtain ⟨hc1, hcz⟩ := legal_after_set _ _ _ _ hz hc
          rcases ih c hc1 z (legal_set_other _ z c _ hz (Ne.symm hcz)) with hw' | hf'
          · exfalso
            rw [← setCell_comm (setCell b m p) z c p (otherPlayer p) (Ne.symm hcz),
              checkWin_other_stone _ c (otherPlayer p) p lines (other_neq p) hc, ew] at hw'
            exact absurd hw' (by decide)
          · rw [setCell_comm (setCell b m p) z c p (otherPlayer p) (Ne.symm hcz)]
            exact hf'
    · -- the strategy move m is still free: play it
      have hm' := legal_set_other b m x p hm hmx
      have hx1 := legal_set_other b x m p hx (Ne.symm hmx)
      have hcomm : setCell (setCell b x p) m p = setCell (setCell b m p) x p :=
        setCell_comm b x m p p (Ne.symm hmx)
      cases ew : checkWin (setCell (setCell b x p) m p) p lines with
      | true => exact ForcesWin.now d _ m hm' ew
      | false =>
        apply ForcesWin.next d _ m hm'
        · obtain ⟨c, hc⟩ := needsMove (hfw x hx1)
          obtain ⟨hc1, hcx⟩ := legal_after_set _ _ _ _ hx1 hc
          exact ⟨c, by rw [hcomm]; exact legal_set_other _ c x p hc1 hcx⟩
        · intro c hc
          rw [hcomm] at hc ⊢
          obtain ⟨hc1, hcx⟩ := legal_after_set _ _ _ _ hx1 hc
          rw [setCell_comm (setCell b m p) x c p (otherPlayer p) (Ne.symm hcx),
            checkWin_other_stone _ x p (otherPlayer p) lines (neq_other p)
              (legal_set_other _ x c _ hx1 (Ne.symm hcx))]
          exact hno c hc1
        · intro c hc
          rw [hcomm] at hc ⊢
          obtain ⟨hc1, hcx⟩ := legal_after_set _ _ _ _ hx1 hc
          rcases ih c hc1 x (legal_set_other _ x c _ hx1 (Ne.symm hcx)) with hw' | hf'
          · exfalso
            rw [← setCell_comm (setCell b m p) x c p (otherPlayer p) (Ne.symm hcx),
              checkWin_other_stone _ c (otherPlayer p) p lines (other_neq p) hc,
              ← hcomm, ew] at hw'
            exact absurd hw' (by decide)
          · rw [setCell_comm (setCell b m p) x c p (otherPlayer p) (Ne.symm hcx)]
            exact hf'

/-- Two players cannot both force a win from the same position. -/
theorem not_both {lines : List (List Nat)} {p : Player} {d : Nat} {b : Board}
    (h : ForcesWin lines p d b) : ∀ d', (∀ m, isLegalMove b m = true →
      checkWin (setCell b m p) p lines = false ∧
      ForcesWin lines (otherPlayer p) d' (setCell b m p)) → False := by
  induction h with
  | now d b m hm hw =>
    intro d' hopp
    have := (hopp m hm).1
    rw [hw] at this
    exact absurd this (by decide)
  | next d b m hm hex hno hfw ih =>
    intro d' hopp
    have hq := (hopp m hm).2
    cases hq with
    | now d1 _ c hc hwq =>
      rw [hno c hc] at hwq
      exact absurd hwq (by decide)
    | next d1 _ c hc hexq hnoq hfwq =>
      apply ih c hc d1
      intro m' hm'
      rw [otherPlayer_involutive] at hnoq hfwq
      exact ⟨hnoq m' hm', hfwq m' hm'⟩

/-- Strategy stealing: on every hypergraph and board size, the second player has
    no forced win from the empty board. -/
theorem strategy_stealing (lines : List (List Nat)) (N d : Nat) :
    ¬ SecondForcesWin lines d (emptyBoard N) := by
  rintro ⟨⟨m0, hm0⟩, hall⟩
  -- colour symmetry: Player 1 answering ANY Player 2 opening wins
  have hsw : ∀ y, isLegalMove (emptyBoard N) y = true →
      checkWin (setCell (emptyBoard N) y .P2) .P2 lines = false ∧
      ForcesWin lines .P1 d (setCell (emptyBoard N) y .P2) := by
    intro y hy
    obtain ⟨hn, hf⟩ := hall y hy
    have hs := forcesWin_swap hf
    rw [← swap_setCell, swap_empty] at hs
    have e1 := checkWin_swap (setCell (emptyBoard N) y .P1) .P1 lines
    rw [← swap_setCell, swap_empty] at e1
    exact ⟨e1.trans hn, hs⟩
  -- Player 1 steals that strategy: open at m0, then pretend it is not there
  have hwin : ForcesWin lines .P1 (d + 1) (emptyBoard N) := by
    cases ew : checkWin (setCell (emptyBoard N) m0 .P1) .P1 lines with
    | true => exact ForcesWin.now d _ m0 hm0 ew
    | false =>
      apply ForcesWin.next d _ m0 hm0
      · exact needsMove (hall m0 hm0).2
      · intro y hy
        obtain ⟨hy0, hne⟩ := legal_after_set _ _ _ _ hm0 hy
        show checkWin (setCell (setCell (emptyBoard N) m0 .P1) y .P2) .P2 lines = false
        rw [setCell_comm (emptyBoard N) m0 y .P1 .P2 (Ne.symm hne),
          checkWin_other_stone _ m0 .P1 .P2 lines (by decide)
            (legal_set_other _ m0 y _ hm0 (Ne.symm hne))]
        exact (hsw y hy0).1
      · intro y hy
        obtain ⟨hy0, hne⟩ := legal_after_set _ _ _ _ hm0 hy
        show ForcesWin lines .P1 d (setCell (setCell (emptyBoard N) m0 .P1) y .P2)
        rcases steal (hsw y hy0).2 m0 (legal_set_other _ m0 y _ hm0 (Ne.symm hne)) with hc | hc
        · exfalso
          rw [← setCell_comm (emptyBoard N) m0 y .P1 .P2 (Ne.symm hne),
            checkWin_other_stone _ y .P2 .P1 lines (by decide) hy, ew] at hc
          exact absurd hc (by decide)
        · rw [setCell_comm (emptyBoard N) m0 y .P1 .P2 (Ne.symm hne)]
          exact hc
  exact not_both hwin d hall

/-- In particular the second player never wins any (m, n, k) game. -/
theorem mnk_second_player_never_wins (m n k d : Nat) :
    ¬ SecondForcesWin (genLines m n k) d (emptyBoard (m * n)) :=
  strategy_stealing _ _ _

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
#print axioms forcesWin_makerWins
#print axioms owned_maker
#print axioms lw_maker
#print axioms lw_breaker
#print axioms phi_maker
#print axioms phi_breaker
#print axioms wgt_breaker_le
#print axioms phi_full
#print axioms breaker_reply_bound
#print axioms erdos_selfridge_potential
#print axioms erdos_selfridge_breaker_second
#print axioms erdos_selfridge_breaker_first
#print axioms erdos_selfridge_draw
#print axioms mnk_prime_triple_11_7_7_draw
#print axioms mnk_prime_triple_17_13_11_draw
#print axioms mnk_prime_triple_19_17_13_draw
#print axioms erdos_selfridge_draw_refined
#print axioms mnk_4_4_4_draw
#print axioms setCell_comm
#print axioms checkWin_other_stone
#print axioms forcesWin_swap
#print axioms steal
#print axioms not_both
#print axioms strategy_stealing
#print axioms mnk_second_player_never_wins
