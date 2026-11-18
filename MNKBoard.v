(** **************************************************************************
    MNKBoard.v: Coordinate Geometry, a Verified Line Generator, and
    Line-Counting Theory for Generalized (m, n, k) Games Without Gravity

    Formalizes the hypergraph of any rectangular m x n grid with threshold k:
    - 2D grid coordinates (r, c) and the flat index r * n + c.
    - An explicit, geometric winning-line generator [gen_lines m n k]
      (horizontal, vertical, main diagonal, anti-diagonal).
    - Universal line-counting theorem: length (gen_lines m n k) equals the
      closed form L(m, n, k) for ALL m, n, k  ([gen_lines_count]).
    - Every generated line has exactly k distinct in-range cells, and the
      Hypergraph Handshaking Identity  sum_x deg(x) = k * L(m, n, k)
      ([mnk_handshaking]).
    - Landmark line counts, and the arithmetic hypothesis of the
      Erdos-Selfridge criterion for "near-square" boards
      ([erdos_selfridge_hypothesis_near_square]).

    Zero axioms, zero admissions (closed under the global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.

Section MNKBoard.

(** 2D Cell Coordinates *)
Definition cell : Type := (nat * nat)%type.

(** Grid containment predicate *)
Definition in_grid (m n : nat) (r c : nat) : bool :=
  (r <? m) && (c <? n).

(** Flat index conversion: (r, c) <-> index *)
Definition coord_to_idx (n : nat) (r c : nat) : nat :=
  r * n + c.

Definition idx_to_row (n : nat) (idx : nat) : nat :=
  idx / n.

Definition idx_to_col (n : nat) (idx : nat) : nat :=
  idx mod n.

(** Lemma: Coordinate encoding is injective and reversible *)
Theorem coord_to_idx_inv : forall n r c : nat,
  0 < n ->
  c < n ->
  idx_to_row n (coord_to_idx n r c) = r /\
  idx_to_col n (coord_to_idx n r c) = c.
Proof.
  intros n r c Hn Hc.
  unfold coord_to_idx, idx_to_row, idx_to_col.
  split.
  - rewrite (Nat.add_comm (r * n) c).
    rewrite Nat.div_add by lia.
    rewrite Nat.div_small by lia.
    lia.
  - rewrite (Nat.add_comm (r * n) c).
    rewrite Nat.Div0.mod_add.
    rewrite Nat.mod_small by lia.
    reflexivity.
Qed.

Lemma idx_div : forall n r c, c < n -> (r * n + c) / n = r.
Proof.
  intros n r c Hc. apply (coord_to_idx_inv n r c); lia.
Qed.

Lemma idx_mod : forall n r c, c < n -> (r * n + c) mod n = c.
Proof.
  intros n r c Hc. apply (coord_to_idx_inv n r c); lia.
Qed.

(** Closed-form formula for line counts *)
Definition horiz_lines_count (m n k : nat) : nat :=
  if k <=? n then m * (n - k + 1) else 0.

Definition vert_lines_count (m n k : nat) : nat :=
  if k <=? m then n * (m - k + 1) else 0.

Definition diag1_lines_count (m n k : nat) : nat :=
  if (k <=? m) && (k <=? n) then (m - k + 1) * (n - k + 1) else 0.

Definition diag2_lines_count (m n k : nat) : nat :=
  if (k <=? m) && (k <=? n) then (m - k + 1) * (n - k + 1) else 0.

Definition total_lines_formula (m n k : nat) : nat :=
  horiz_lines_count m n k +
  vert_lines_count m n k +
  diag1_lines_count m n k +
  diag2_lines_count m n k.

(** Algebraic normal form of the formula when k <= min(m, n).
    (This only unfolds the definition; the theorem that the formula really
    counts the lines of the grid is [gen_lines_count] below.) *)
Theorem mnk_line_count_formula_closed : forall m n k : nat,
  k <= m ->
  k <= n ->
  total_lines_formula m n k =
    m * (n - k + 1) + n * (m - k + 1) + 2 * (m - k + 1) * (n - k + 1).
Proof.
  intros m n k Hm Hn.
  unfold total_lines_formula, horiz_lines_count, vert_lines_count,
         diag1_lines_count, diag2_lines_count.
  apply Nat.leb_le in Hm.
  apply Nat.leb_le in Hn.
  rewrite Hm, Hn. simpl.
  lia.
Qed.

(* ========================================================================= *)
(** * Verified geometric line generator                                       *)
(* ========================================================================= *)

Inductive direction : Type := DH | DV | DD | DA.

(** The i-th cell (row, column) of the line of direction d whose bounding box
    has top-left corner (r, c).  DA runs from bottom-left to top-right. *)
Definition cell_at (k : nat) (d : direction) (r c i : nat) : nat * nat :=
  match d with
  | DH => (r, c + i)
  | DV => (r + i, c)
  | DD => (r + i, c + i)
  | DA => (r + (k - 1 - i), c + i)
  end.

Definition mkline (n k : nat) (d : direction) (r c : nat) : list nat :=
  map (fun i => fst (cell_at k d r c i) * n + snd (cell_at k d r c i)) (seq 0 k).

(** A line with bounding-box corner (r, c) fits inside the m x n grid. *)
Definition fits (m n k : nat) (d : direction) (r c : nat) : Prop :=
  match d with
  | DH => r < m /\ c + k <= n
  | DV => r + k <= m /\ c < n
  | DD | DA => r + k <= m /\ c + k <= n
  end.

Definition starts (m n k : nat) (d : direction) : list (nat * nat) :=
  match d with
  | DH => if k <=? n then list_prod (seq 0 m) (seq 0 (n - k + 1)) else []
  | DV => if k <=? m then list_prod (seq 0 (m - k + 1)) (seq 0 n) else []
  | DD | DA => if (k <=? m) && (k <=? n)
               then list_prod (seq 0 (m - k + 1)) (seq 0 (n - k + 1)) else []
  end.

Definition all_directions : list direction := [DH; DV; DD; DA].

Definition gen_lines (m n k : nat) : list (list nat) :=
  flat_map (fun d => map (fun rc => mkline n k d (fst rc) (snd rc)) (starts m n k d))
           all_directions.

Lemma in_starts : forall m n k d r c,
  In (r, c) (starts m n k d) <-> fits m n k d r c.
Proof.
  intros m n k d r c.
  destruct d; unfold starts, fits.
  - destruct (k <=? n) eqn:E; [apply Nat.leb_le in E | apply Nat.leb_gt in E].
    + rewrite in_prod_iff, !in_seq. lia.
    + simpl. lia.
  - destruct (k <=? m) eqn:E; [apply Nat.leb_le in E | apply Nat.leb_gt in E].
    + rewrite in_prod_iff, !in_seq. lia.
    + simpl. lia.
  - destruct (k <=? m) eqn:E1; [apply Nat.leb_le in E1 | apply Nat.leb_gt in E1];
    destruct (k <=? n) eqn:E2; [apply Nat.leb_le in E2 | apply Nat.leb_gt in E2 |
                                apply Nat.leb_le in E2 | apply Nat.leb_gt in E2];
    simpl; try rewrite in_prod_iff, !in_seq; lia.
  - destruct (k <=? m) eqn:E1; [apply Nat.leb_le in E1 | apply Nat.leb_gt in E1];
    destruct (k <=? n) eqn:E2; [apply Nat.leb_le in E2 | apply Nat.leb_gt in E2 |
                                apply Nat.leb_le in E2 | apply Nat.leb_gt in E2];
    simpl; try rewrite in_prod_iff, !in_seq; lia.
Qed.

(** Characterization: the generated lines are exactly the fitting lines. *)
Theorem in_gen_lines : forall m n k L,
  In L (gen_lines m n k) <->
  exists d r c, fits m n k d r c /\ L = mkline n k d r c.
Proof.
  intros m n k L. unfold gen_lines. rewrite in_flat_map. split.
  - intros [d [_ H]]. apply in_map_iff in H as [[r c] [HL Hin]].
    apply in_starts in Hin. exists d, r, c. simpl in HL. auto.
  - intros (d & r & c & Hf & ->). exists d. split.
    + destruct d; simpl; tauto.
    + apply in_map_iff. exists (r, c). split; [reflexivity|].
      apply in_starts. exact Hf.
Qed.

(** Universal Line-Counting Theorem: the generator produces exactly
    L(m, n, k) lines, for every m, n, k. *)
Theorem gen_lines_count : forall m n k,
  length (gen_lines m n k) = total_lines_formula m n k.
Proof.
  intros m n k.
  unfold gen_lines, all_directions, total_lines_formula, horiz_lines_count,
    vert_lines_count, diag1_lines_count, diag2_lines_count.
  cbn [flat_map]. rewrite !length_app, !length_map. cbn [starts].
  destruct (k <=? n), (k <=? m); cbn [andb];
    rewrite ?length_prod, ?length_seq; cbn [length]; lia.
Qed.

Lemma cell_at_bounds : forall m n k d r c i,
  fits m n k d r c -> i < k ->
  r <= fst (cell_at k d r c i) < r + k /\ fst (cell_at k d r c i) < m /\
  c <= snd (cell_at k d r c i) < c + k /\ snd (cell_at k d r c i) < n.
Proof.
  intros m n k d r c i Hf Hi.
  destruct d; simpl in *; lia.
Qed.

Lemma mkline_length : forall n k d r c, length (mkline n k d r c) = k.
Proof.
  intros. unfold mkline. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma in_mkline : forall n k d r c x,
  In x (mkline n k d r c) <->
  exists i, i < k /\ x = fst (cell_at k d r c i) * n + snd (cell_at k d r c i).
Proof.
  intros. unfold mkline. rewrite in_map_iff. split.
  - intros [i [Hx Hi]]. apply in_seq in Hi. exists i. split; [lia | auto].
  - intros [i [Hi Hx]]. exists i. split; [auto | apply in_seq; lia].
Qed.

(** Decoding a cell of a fitting line back into (row, column). *)
Lemma mkline_decode : forall m n k d r c x,
  fits m n k d r c -> In x (mkline n k d r c) ->
  exists i, i < k /\ x / n = fst (cell_at k d r c i) /\
            x mod n = snd (cell_at k d r c i) /\ x < m * n.
Proof.
  intros m n k d r c x Hf Hx.
  apply in_mkline in Hx as [i [Hi ->]].
  pose proof (cell_at_bounds m n k d r c i Hf Hi) as B.
  exists i. repeat split; try lia.
  - apply idx_div. lia.
  - apply idx_mod. lia.
  - nia.
Qed.

(** Bounding box: all cells of a line lie within k-1 rows and k-1 columns
    of each other. *)
Lemma gen_lines_bounding_box : forall m n k L x y,
  In L (gen_lines m n k) -> In x L -> In y L ->
  x / n < y / n + k /\ x mod n < y mod n + k.
Proof.
  intros m n k L x y HL Hx Hy.
  apply in_gen_lines in HL as (d & r & c & Hf & ->).
  destruct (mkline_decode m n k d r c x Hf Hx) as (i & Hi & Hxr & Hxc & _).
  destruct (mkline_decode m n k d r c y Hf Hy) as (j & Hj & Hyr & Hyc & _).
  pose proof (cell_at_bounds m n k d r c i Hf Hi).
  pose proof (cell_at_bounds m n k d r c j Hf Hj).
  lia.
Qed.

Lemma gen_lines_in_range : forall m n k L x,
  In L (gen_lines m n k) -> In x L -> x < m * n.
Proof.
  intros m n k L x HL Hx.
  apply in_gen_lines in HL as (d & r & c & Hf & ->).
  destruct (mkline_decode m n k d r c x Hf Hx) as (i & _ & _ & _ & H). exact H.
Qed.

Lemma gen_lines_uniform : forall m n k L,
  In L (gen_lines m n k) -> length L = k.
Proof.
  intros m n k L HL.
  apply in_gen_lines in HL as (d & r & c & _ & ->). apply mkline_length.
Qed.

Lemma gen_lines_nodup : forall m n k L,
  In L (gen_lines m n k) -> NoDup L.
Proof.
  intros m n k L HL.
  apply in_gen_lines in HL as (d & r & c & Hf & ->).
  unfold mkline. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros i j Hi Hj Heq. apply in_seq in Hi. apply in_seq in Hj.
  pose proof (cell_at_bounds m n k d r c i Hf ltac:(lia)) as Bi.
  pose proof (cell_at_bounds m n k d r c j Hf ltac:(lia)) as Bj.
  cbv beta in Heq.
  assert (Hc : snd (cell_at k d r c i) = snd (cell_at k d r c j)).
  { transitivity ((fst (cell_at k d r c i) * n + snd (cell_at k d r c i)) mod n).
    - symmetry. apply idx_mod. lia.
    - rewrite Heq. apply idx_mod. lia. }
  assert (Hr : fst (cell_at k d r c i) = fst (cell_at k d r c j)).
  { transitivity ((fst (cell_at k d r c i) * n + snd (cell_at k d r c i)) / n).
    - symmetry. apply idx_div. lia.
    - rewrite Heq. apply idx_div. lia. }
  destruct d; simpl in *; lia.
Qed.

(* ========================================================================= *)
(** * Hypergraph Handshaking Identity                                         *)
(* ========================================================================= *)

Definition degree (lines : list (list nat)) (x : nat) : nat :=
  length (filter (fun l => existsb (Nat.eqb x) l) lines).

Lemma count_members : forall (l : list nat) N,
  NoDup l -> (forall x, In x l -> x < N) ->
  length (filter (fun x => existsb (Nat.eqb x) l) (seq 0 N)) = length l.
Proof.
  intros l N Hnd Hr.
  set (f := filter (fun x => existsb (Nat.eqb x) l) (seq 0 N)).
  assert (Hf : forall x, In x f <-> In x l).
  { intros x. unfold f. rewrite filter_In, in_seq, existsb_exists. split.
    - intros [_ [y [Hy Hxy]]]. apply Nat.eqb_eq in Hxy. subst. exact Hy.
    - intros Hx. split; [specialize (Hr x Hx); lia |].
      exists x. split; [exact Hx | apply Nat.eqb_refl]. }
  assert (Hnf : NoDup f) by (apply NoDup_filter, seq_NoDup).
  apply Nat.le_antisymm; apply NoDup_incl_length; auto;
    intros x Hx; apply Hf; auto.
Qed.

Lemma degree_cons : forall l ls x,
  degree (l :: ls) x = (if existsb (Nat.eqb x) l then 1 else 0) + degree ls x.
Proof.
  intros. unfold degree. simpl. destruct (existsb (Nat.eqb x) l); reflexivity.
Qed.

Lemma sum_map_add : forall (f g : nat -> nat) xs,
  list_sum (map (fun x => f x + g x) xs) = list_sum (map f xs) + list_sum (map g xs).
Proof.
  intros f g xs. induction xs as [| x xs IH]; simpl; [reflexivity | rewrite IH; lia].
Qed.

Lemma sum_indicator : forall (f : nat -> bool) xs,
  list_sum (map (fun x => if f x then 1 else 0) xs) = length (filter f xs).
Proof.
  intros f xs. induction xs as [| x xs IH]; simpl; [reflexivity |].
  destruct (f x); simpl; rewrite IH; reflexivity.
Qed.

Lemma handshaking_generic : forall (lines : list (list nat)) N,
  (forall l, In l lines -> NoDup l /\ forall x, In x l -> x < N) ->
  list_sum (map (degree lines) (seq 0 N)) = list_sum (map (@length nat) lines).
Proof.
  induction lines as [| l ls IH]; intros N H.
  - unfold degree. simpl. induction (seq 0 N); simpl; auto.
  - rewrite (map_ext _ _ (degree_cons l ls)).
    rewrite sum_map_add, sum_indicator.
    destruct (H l (or_introl eq_refl)) as [Hnd Hr].
    rewrite (count_members l N Hnd Hr).
    rewrite (IH N) by (intros; apply H; right; auto).
    reflexivity.
Qed.

(** Handshaking: the sum of the degrees of all m * n cells is k * L(m, n, k). *)
Theorem mnk_handshaking : forall m n k,
  list_sum (map (degree (gen_lines m n k)) (seq 0 (m * n))) =
  k * total_lines_formula m n k.
Proof.
  intros m n k.
  rewrite handshaking_generic.
  - rewrite <- gen_lines_count.
    assert (H : forall ls : list (list nat), (forall l, In l ls -> length l = k) ->
              list_sum (map (@length nat) ls) = k * length ls).
    { induction ls as [| l ls IH]; intros Hk; simpl; [lia |].
      rewrite (Hk l (or_introl eq_refl)).
      rewrite IH by (intros; apply Hk; right; assumption). lia. }
    apply H. intros l Hl. eapply gen_lines_uniform; eauto.
  - intros l Hl. split; [eapply gen_lines_nodup; eauto |].
    intros x Hx. eapply gen_lines_in_range; eauto.
Qed.

(* ========================================================================= *)
(** * Landmark instances                                                      *)
(* ========================================================================= *)

Theorem mnk_3_3_3_lines : total_lines_formula 3 3 3 = 8.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_3_4_3_lines : total_lines_formula 3 4 3 = 14.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_4_4_4_lines : total_lines_formula 4 4 4 = 10.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_5_4_4_lines : total_lines_formula 5 4 4 = 17.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_6_4_4_lines : total_lines_formula 6 4 4 = 24.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_7_4_4_lines : total_lines_formula 7 4 4 = 31.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_8_4_4_lines : total_lines_formula 8 4 4 = 38.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_5_5_4_lines : total_lines_formula 5 5 4 = 28.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_8_8_5_lines : total_lines_formula 8 8 5 = 96.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_15_15_5_gomoku_lines : total_lines_formula 15 15 5 = 572.
Proof. vm_compute. reflexivity. Qed.

(** Consecutive prime triples (p_{i+2}, p_{i+1}, p_i) and related instances *)

Theorem mnk_prime_triple_7_5_3_lines : total_lines_formula 7 5 3 = 76.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_prime_triple_11_7_5_lines : total_lines_formula 11 7 5 = 124.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_prime_triple_13_11_7_lines : total_lines_formula 13 11 7 = 212.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_prime_triple_11_7_7_lines : total_lines_formula 11 7 7 = 56.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_prime_triple_17_13_11_lines : total_lines_formula 17 13 11 = 184.
Proof. vm_compute. reflexivity. Qed.

Theorem mnk_prime_triple_19_17_13_lines : total_lines_formula 19 17 13 = 284.
Proof. vm_compute. reflexivity. Qed.

(** The following three theorems verify ONLY the arithmetic hypothesis
    |E| < 2^(k-1) of the Erdos-Selfridge criterion (1973) for the k-uniform
    hypergraph of winning lines.  The game-theoretic consequence (Player 2 can
    block every line, hence by strategy stealing the game is a draw) is a
    classical theorem that is cited, NOT formalized, in this development. *)

Theorem mnk_prime_triple_11_7_7_erdos_bound :
  total_lines_formula 11 7 7 < 2^(7 - 1).
Proof. vm_compute. lia. Qed.

Theorem mnk_prime_triple_17_13_11_erdos_bound :
  total_lines_formula 17 13 11 < 2^(11 - 1).
Proof. vm_compute. lia. Qed.

Theorem mnk_prime_triple_19_17_13_erdos_bound :
  total_lines_formula 19 17 13 < 2^(13 - 1).
Proof. vm_compute. lia. Qed.

(** Universal version: for every board with k <= n, m < 2k and k >= 11 the
    line count is below the Erdos-Selfridge threshold 2^(k-1).  For a
    consecutive prime triple p < q < r with p >= 7 one has r < 2p
    (Ramanujan, 1919: the 2nd Ramanujan prime is 11), so every triple
    (r, q, p) with p >= 11 satisfies these hypotheses. *)

Lemma six_sq_lt_pow2 : forall k, 11 <= k -> 6 * (k * k) < 2 ^ (k - 1).
Proof.
  intros k Hk.
  replace k with (11 + (k - 11)) by lia.
  generalize (k - 11) as j. clear k Hk.
  induction j as [| j IH].
  - vm_compute. lia.
  - replace (11 + S j - 1) with (S (11 + j - 1)) by lia.
    rewrite Nat.pow_succ_r'. nia.
Qed.

Theorem erdos_selfridge_hypothesis_near_square : forall m n k,
  11 <= k -> k <= n -> k <= m -> n < 2 * k -> m < 2 * k ->
  total_lines_formula m n k < 2 ^ (k - 1).
Proof.
  intros m n k Hk Hn Hm Hn2 Hm2.
  rewrite mnk_line_count_formula_closed by lia.
  pose proof (six_sq_lt_pow2 k Hk).
  assert (Ha : m - k + 1 <= k) by lia.
  assert (Hb : n - k + 1 <= k) by lia.
  assert (m * (n - k + 1) <= 2 * k * k) by nia.
  assert (n * (m - k + 1) <= 2 * k * k) by nia.
  assert (2 * (m - k + 1) * (n - k + 1) <= 2 * k * k) by nia.
  lia.
Qed.

(* ========================================================================= *)
(** * Concrete line lists for (3, 3, 3) and (3, 4, 3)                         *)
(* ========================================================================= *)

Definition lines_3_3_3 : list (list nat) :=
  [ [0; 1; 2]; [3; 4; 5]; [6; 7; 8];
    [0; 3; 6]; [1; 4; 7]; [2; 5; 8];
    [0; 4; 8]; [2; 4; 6] ].

Theorem lines_3_3_3_count : length lines_3_3_3 = 8.
Proof. reflexivity. Qed.

Definition lines_3_4_3 : list (list nat) :=
  [ (* Horizontals *)
    [0; 1; 2]; [1; 2; 3];
    [4; 5; 6]; [5; 6; 7];
    [8; 9; 10]; [9; 10; 11];
    (* Verticals *)
    [0; 4; 8]; [1; 5; 9]; [2; 6; 10]; [3; 7; 11];
    (* Diagonals down-right *)
    [0; 5; 10]; [1; 6; 11];
    (* Diagonals up-right *)
    [8; 5; 2]; [9; 6; 3] ].

Theorem lines_3_4_3_count : length lines_3_4_3 = 14.
Proof. reflexivity. Qed.

Theorem lines_3_4_3_all_len_3 : forall l,
  In l lines_3_4_3 -> length l = 3.
Proof.
  intros l Hin.
  repeat (destruct Hin as [Heq | Hin]; [subst l; reflexivity |]);
  destruct Hin.
Qed.

(** The hand-written lists are exactly the generated hypergraphs. *)
Theorem lines_3_3_3_generated : gen_lines 3 3 3 =
  [ [0; 1; 2]; [3; 4; 5]; [6; 7; 8];
    [0; 3; 6]; [1; 4; 7]; [2; 5; 8];
    [0; 4; 8]; [6; 4; 2] ].
Proof. vm_compute. reflexivity. Qed.

Theorem lines_3_4_3_generated : gen_lines 3 4 3 =
  [ [0; 1; 2]; [1; 2; 3]; [4; 5; 6]; [5; 6; 7]; [8; 9; 10]; [9; 10; 11];
    [0; 4; 8]; [1; 5; 9]; [2; 6; 10]; [3; 7; 11];
    [0; 5; 10]; [1; 6; 11];
    [8; 5; 2]; [9; 6; 3] ].
Proof. vm_compute. reflexivity. Qed.

(** Strip Obstruction Theorem:
    On any strip of width n < k, there are no horizontal and no diagonal lines. *)
Theorem strip_width_horizontal_obstruction : forall m n k : nat,
  n < k ->
  horiz_lines_count m n k = 0.
Proof.
  intros m n k Hn.
  unfold horiz_lines_count.
  apply Nat.leb_gt in Hn.
  rewrite Hn. reflexivity.
Qed.

Theorem strip_width_diagonal_obstruction : forall m n k : nat,
  n < k ->
  diag1_lines_count m n k = 0 /\ diag2_lines_count m n k = 0.
Proof.
  intros m n k Hn.
  unfold diag1_lines_count, diag2_lines_count.
  apply Nat.leb_gt in Hn.
  rewrite Hn.
  rewrite andb_false_r.
  split; reflexivity.
Qed.

End MNKBoard.
