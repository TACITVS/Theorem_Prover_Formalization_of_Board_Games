(** * MNKErdosSelfridge.v: The Erdős–Selfridge Theorem, Machine-Checked

    Erdős and Selfridge (1973): in the Maker–Breaker game on a hypergraph
    whose edges [A] satisfy  sum_A 2^(-|A|) < 1/2,  Breaker, moving second,
    can prevent Maker from ever claiming a whole edge.  If Breaker moves
    first, sum_A 2^(-|A|) < 1 suffices.

    The proof is the classical potential-function (derandomization) argument.
    All weights are scaled by 2^K, where K bounds every edge size, so the
    whole development stays in [nat]:

      lw(L)  = 2^(K - |L| + #Maker stones on L)   if L carries no Breaker stone
               0                                   otherwise
      phi    = sum of lw(L) over all lines
      wgt(x) = sum of lw(L) over the lines L through x

    A Maker move at x adds exactly wgt(x) to phi; a Breaker move at x removes
    exactly wgt(x) and never increases any wgt(y).  Breaker always answers on
    a cell of maximal weight, which keeps  phi + wgt(y) < 2^K  for every empty
    y, whereas a line completed by Maker alone contributes 2^K.

    Main results:
      - [erdos_selfridge_breaker_second] / [erdos_selfridge_breaker_first]:
        the Maker–Breaker theorem for arbitrary (non-uniform) hypergraphs.
      - [erdos_selfridge_draw]: in the strong game, sum_A 2^(-|A|) < 1/2
        makes the game a draw (no strategy stealing needed: each player
        uses the Breaker strategy against the other).
      - [mnk_erdos_selfridge_draw]: L(m, n, k) < 2^(k-1) implies that the
        (m, n, k) game is a draw; hence the formal draws of (11,7,7),
        (17,13,11), (19,17,13), of every near-square board with k >= 11, and
        of every (k, k, k) board with k >= 5.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame.

(* ========================================================================= *)
(** * 1. Maker–Breaker semantics                                             *)
(* ========================================================================= *)

(** [maker_wins lines p d b]: Maker [p], to move on [b], claims a whole line
    within [d] of its own moves against every legal Breaker reply.  Breaker's
    own lines are irrelevant; a board filled without a Maker line is a Breaker
    win, so a continuation must leave Breaker a legal reply. *)
Inductive maker_wins (lines : list (list nat)) (p : player) : nat -> board_t -> Prop :=
  | mw_now : forall d b m,
      is_legal_move b m = true ->
      check_win (set_cell b m p) p lines = true ->
      maker_wins lines p (S d) b
  | mw_next : forall d b m,
      is_legal_move b m = true ->
      (exists c, is_legal_move (set_cell b m p) c = true) ->
      (forall c, is_legal_move (set_cell b m p) c = true ->
         maker_wins lines p d (set_cell (set_cell b m p) c (other_player p))) ->
      maker_wins lines p (S d) b.

(** A forced win in the strong game is in particular a Maker win. *)
Theorem forces_win_maker_wins : forall lines p d b,
  forces_win lines p d b -> maker_wins lines p d b.
Proof.
  intros lines p d b H.
  induction H as [d b m Hm Hw | d b m Hm Hex Hno Hfw IH].
  - eapply mw_now; eassumption.
  - eapply mw_next; eassumption.
Qed.

(* ========================================================================= *)
(** * 2. Arithmetic and board helpers                                        *)
(* ========================================================================= *)

Lemma ls_cons : forall (A : Type) (f : A -> nat) a l,
  list_sum (map f (a :: l)) = f a + list_sum (map f l).
Proof. reflexivity. Qed.

Lemma ls_plus : forall (A : Type) (f g : A -> nat) l,
  list_sum (map (fun x => f x + g x) l) = list_sum (map f l) + list_sum (map g l).
Proof.
  intros A f g l. induction l as [| a l IH]; [reflexivity |].
  rewrite !ls_cons, IH. lia.
Qed.

Lemma ls_le : forall (A : Type) (f g : A -> nat) l,
  (forall x, In x l -> f x <= g x) -> list_sum (map f l) <= list_sum (map g l).
Proof.
  intros A f g l H. induction l as [| a l IH]; [simpl; lia |].
  rewrite !ls_cons.
  assert (f a <= g a) by (apply H; left; reflexivity).
  assert (list_sum (map f l) <= list_sum (map g l))
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  lia.
Qed.

Lemma ls_ext : forall (A : Type) (f g : A -> nat) l,
  (forall x, In x l -> f x = g x) -> list_sum (map f l) = list_sum (map g l).
Proof. intros A f g l H. f_equal. apply map_ext_in. exact H. Qed.

Lemma ls_member : forall (A : Type) (f : A -> nat) l a,
  In a l -> f a <= list_sum (map f l).
Proof.
  intros A f l a H. induction l as [| x l IH]; [destruct H |].
  rewrite ls_cons. destruct H as [-> | H]; [lia |]. specialize (IH H). lia.
Qed.

Lemma eqb_other_l : forall p, player_eqb (other_player p) p = false.
Proof. destruct p; reflexivity. Qed.

Lemma owned_set : forall b x r s y, x < length b ->
  cell_owned_by (set_cell b x r) s y =
  if Nat.eqb y x then player_eqb s r else cell_owned_by b s y.
Proof.
  intros b x r s y Hx. unfold cell_owned_by.
  destruct (Nat.eqb_spec y x) as [Heq | Hne].
  - subst y. rewrite get_set_cell_same by exact Hx. reflexivity.
  - rewrite get_set_cell_other by congruence. reflexivity.
Qed.

Lemma owned_empty_cell : forall b s x,
  get_cell b x = None -> cell_owned_by b s x = false.
Proof. intros b s x H. unfold cell_owned_by. rewrite H. reflexivity. Qed.

Lemma existsb_eqb_In : forall x L, existsb (Nat.eqb x) L = true <-> In x L.
Proof.
  intros x L. rewrite existsb_exists. split.
  - intros [y [Hy Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hy.
  - intros H. exists x. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma forallb_ext_in' : forall (f g : nat -> bool) l,
  (forall y, In y l -> f y = g y) -> forallb f l = forallb g l.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma forallb_false_in : forall (f : nat -> bool) l x,
  In x l -> f x = false -> forallb f l = false.
Proof.
  intros f l x Hx Hf. destruct (forallb f l) eqn:E; [| reflexivity].
  rewrite forallb_forall in E. rewrite (E x Hx) in Hf. discriminate.
Qed.

Lemma filter_all_true : forall (f : nat -> bool) l,
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros f l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)).
  rewrite IH by (intros x Hx; apply H; right; exact Hx). reflexivity.
Qed.

Lemma filter_all_false : forall (f : nat -> bool) l,
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros f l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)).
  apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma legal_after_set : forall b c r y,
  is_legal_move b c = true ->
  is_legal_move (set_cell b c r) y = true -> is_legal_move b y = true.
Proof.
  intros b c r y Hc Hy.
  pose proof (legal_move_lt _ _ Hy) as Hlt. rewrite set_cell_length in Hlt.
  pose proof (legal_move_empty _ _ Hy) as He.
  apply legal_move_intro; [exact Hlt |].
  destruct (Nat.eq_dec c y) as [Heq | Hne].
  - subst y. rewrite get_set_cell_same in He by (apply legal_move_lt; exact Hc).
    discriminate.
  - rewrite get_set_cell_other in He by exact Hne. exact He.
Qed.

Lemma argmax_in : forall (f : nat -> nat) l,
  l <> [] -> exists c, In c l /\ forall y, In y l -> f y <= f c.
Proof.
  intros f l. induction l as [| a l IH]; intros Hne; [congruence |].
  destruct l as [| a' l'].
  - exists a. split; [left; reflexivity |]. intros y [Hy | []]. subst y. lia.
  - assert (Hne2 : a' :: l' <> []) by discriminate.
    destruct (IH Hne2) as [c [Hc Hmax]].
    destruct (Nat.le_ge_cases (f a) (f c)) as [H | H].
    + exists c. split; [right; exact Hc |].
      intros y [Hy | Hy]; [subst y; exact H | apply Hmax; exact Hy].
    + exists a. split; [left; reflexivity |].
      intros y [Hy | Hy]; [subst y; lia | specialize (Hmax y Hy); lia].
Qed.

(* ========================================================================= *)
(** * 3. The potential                                                       *)
(* ========================================================================= *)

(** A line is alive for Maker [p] when Breaker owns none of its cells. *)
Definition alive (b : board_t) (p : player) (L : list nat) : bool :=
  forallb (fun x => negb (cell_owned_by b (other_player p) x)) L.

Definition owned (b : board_t) (p : player) (L : list nat) : nat :=
  length (filter (cell_owned_by b p) L).

(** Scaled weight 2^K * 2^(-(number of cells of L still to be claimed)). *)
Definition lw (K : nat) (b : board_t) (p : player) (L : list nat) : nat :=
  if alive b p L then 2 ^ (K - length L + owned b p L) else 0.

Definition phi (K : nat) (b : board_t) (p : player) (lines : list (list nat)) : nat :=
  list_sum (map (lw K b p) lines).

Definition through (x : nat) (L : list nat) : bool := existsb (Nat.eqb x) L.

Definition wgt (K : nat) (b : board_t) (p : player) (lines : list (list nat)) (x : nat) : nat :=
  list_sum (map (fun L => if through x L then lw K b p L else 0) lines).

Lemma alive_maker : forall b x p L, is_legal_move b x = true ->
  alive (set_cell b x p) p L = alive b p L.
Proof.
  intros b x p L Hx. unfold alive. apply forallb_ext_in'. intros y _. cbv beta.
  rewrite owned_set by (apply legal_move_lt; exact Hx).
  destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. subst y.
  rewrite eqb_other_l.
  rewrite owned_empty_cell by (apply legal_move_empty; exact Hx). reflexivity.
Qed.

Lemma owned_maker : forall b x p L, is_legal_move b x = true -> NoDup L ->
  owned (set_cell b x p) p L = (if through x L then 1 else 0) + owned b p L.
Proof.
  intros b x p L Hx Hnd. unfold owned, through.
  destruct (existsb (Nat.eqb x) L) eqn:E.
  - apply existsb_eqb_In in E.
    rewrite (filter_length_drop_one L (cell_owned_by (set_cell b x p) p)
               (cell_owned_by b p) x Hnd E).
    + reflexivity.
    + rewrite owned_set by (apply legal_move_lt; exact Hx).
      rewrite Nat.eqb_refl. apply player_eqb_refl.
    + apply owned_empty_cell, legal_move_empty, Hx.
    + intros y Hy. rewrite owned_set by (apply legal_move_lt; exact Hx).
      apply Nat.eqb_neq in Hy. rewrite Hy. reflexivity.
  - replace ((if false then 1 else 0) + length (filter (cell_owned_by b p) L))
      with (length (filter (cell_owned_by b p) L)) by reflexivity.
    f_equal. apply filter_ext_in. intros y Hy.
    rewrite owned_set by (apply legal_move_lt; exact Hx).
    destruct (Nat.eqb_spec y x) as [Heq | _]; [| reflexivity].
    subst y. exfalso.
    assert (existsb (Nat.eqb x) L = true) by (apply existsb_eqb_In; exact Hy).
    congruence.
Qed.

(** A Maker move at [x] doubles the weight of every live line through [x]. *)
Lemma lw_maker : forall K b x p L, is_legal_move b x = true -> NoDup L ->
  lw K (set_cell b x p) p L = lw K b p L + (if through x L then lw K b p L else 0).
Proof.
  intros K b x p L Hx Hnd. unfold lw.
  rewrite alive_maker by exact Hx. rewrite owned_maker by assumption.
  destruct (alive b p L); destruct (through x L); simpl; try lia.
  rewrite Nat.add_succ_r, Nat.pow_succ_r'. lia.
Qed.

(** A Breaker move at [x] kills every line through [x] and nothing else. *)
Lemma lw_breaker : forall K b x p L, is_legal_move b x = true ->
  lw K (set_cell b x (other_player p)) p L = if through x L then 0 else lw K b p L.
Proof.
  intros K b x p L Hx. unfold lw, through.
  destruct (existsb (Nat.eqb x) L) eqn:E.
  - apply existsb_eqb_In in E.
    replace (alive (set_cell b x (other_player p)) p L) with false; [reflexivity |].
    symmetry. unfold alive. apply (forallb_false_in _ L x E). cbv beta.
    rewrite owned_set by (apply legal_move_lt; exact Hx).
    rewrite Nat.eqb_refl, player_eqb_refl. reflexivity.
  - assert (Hin : forall y, In y L -> Nat.eqb y x = false).
    { intros y Hy. apply Nat.eqb_neq. intros Heq. subst y.
      assert (existsb (Nat.eqb x) L = true) by (apply existsb_eqb_In; exact Hy).
      congruence. }
    replace (alive (set_cell b x (other_player p)) p L) with (alive b p L).
    2:{ symmetry. unfold alive. apply forallb_ext_in'. intros y Hy. cbv beta.
        rewrite owned_set by (apply legal_move_lt; exact Hx).
        rewrite (Hin y Hy). reflexivity. }
    replace (owned (set_cell b x (other_player p)) p L) with (owned b p L).
    2:{ symmetry. unfold owned. f_equal. apply filter_ext_in. intros y Hy.
        rewrite owned_set by (apply legal_move_lt; exact Hx).
        rewrite (Hin y Hy). reflexivity. }
    reflexivity.
Qed.

Lemma phi_maker : forall K b x p lines,
  (forall L, In L lines -> NoDup L) -> is_legal_move b x = true ->
  phi K (set_cell b x p) p lines = phi K b p lines + wgt K b p lines x.
Proof.
  intros K b x p lines Hnd Hx. unfold phi, wgt. rewrite <- ls_plus.
  apply ls_ext. intros L HL. cbv beta.
  apply lw_maker; [exact Hx | apply Hnd; exact HL].
Qed.

Lemma phi_breaker : forall K b x p lines, is_legal_move b x = true ->
  phi K (set_cell b x (other_player p)) p lines + wgt K b p lines x = phi K b p lines.
Proof.
  intros K b x p lines Hx. unfold phi, wgt. rewrite <- ls_plus.
  apply ls_ext. intros L _. cbv beta.
  rewrite lw_breaker by exact Hx. destruct (through x L); lia.
Qed.

Lemma wgt_breaker_le : forall K b x p lines y, is_legal_move b x = true ->
  wgt K (set_cell b x (other_player p)) p lines y <= wgt K b p lines y.
Proof.
  intros K b x p lines y Hx. unfold wgt. apply ls_le. intros L _. cbv beta.
  rewrite lw_breaker by exact Hx.
  destruct (through y L); destruct (through x L); lia.
Qed.

Lemma wgt_le_phi : forall K b p lines x, wgt K b p lines x <= phi K b p lines.
Proof.
  intros K b p lines x. unfold wgt, phi. apply ls_le. intros L _. cbv beta.
  destruct (through x L); lia.
Qed.

(** A line claimed entirely by Maker carries the full weight 2^K. *)
Lemma full_line_weight : forall K b p L, length L <= K ->
  (forall y, In y L -> get_cell b y = Some p) -> lw K b p L = 2 ^ K.
Proof.
  intros K b p L HK Hown.
  assert (Ha : alive b p L = true).
  { unfold alive. apply forallb_forall. intros y Hy. cbv beta.
    unfold cell_owned_by. rewrite (Hown y Hy), eqb_other_l. reflexivity. }
  assert (Ho : owned b p L = length L).
  { unfold owned. rewrite filter_all_true; [reflexivity |].
    intros y Hy. unfold cell_owned_by. rewrite (Hown y Hy). apply player_eqb_refl. }
  unfold lw. rewrite Ha, Ho. f_equal. lia.
Qed.

Lemma phi_full : forall K b p lines L, In L lines -> length L <= K ->
  (forall y, In y L -> get_cell b y = Some p) -> 2 ^ K <= phi K b p lines.
Proof.
  intros K b p lines L HL HK Hown. unfold phi.
  pose proof (ls_member _ (lw K b p) lines L HL) as H.
  rewrite (full_line_weight K b p L HK Hown) in H. exact H.
Qed.

Lemma lw_empty : forall K N p L, lw K (empty_board N) p L = 2 ^ (K - length L).
Proof.
  intros K N p L.
  assert (Ha : alive (empty_board N) p L = true).
  { unfold alive. apply forallb_forall. intros y _. cbv beta.
    rewrite owned_empty_cell by apply get_cell_empty_board. reflexivity. }
  assert (Ho : owned (empty_board N) p L = 0).
  { unfold owned. rewrite filter_all_false; [reflexivity |].
    intros y _. apply owned_empty_cell, get_cell_empty_board. }
  unfold lw. rewrite Ha, Ho, Nat.add_0_r. reflexivity.
Qed.

(* ========================================================================= *)
(** * 4. The Erdős–Selfridge theorem                                         *)
(* ========================================================================= *)

Section ErdosSelfridge.

Variable lines : list (list nat).
Variable K : nat.
Hypothesis Hlines : forall L, In L lines -> NoDup L /\ length L <= K.

(** [es_sum] = 2^K * sum over lines of 2^(-|L|). *)
Definition es_sum : nat := list_sum (map (fun L => 2 ^ (K - length L)) lines).

Lemma phi_empty : forall N p, phi K (empty_board N) p lines = es_sum.
Proof.
  intros N p. unfold phi, es_sum. apply ls_ext. intros L _. apply lw_empty.
Qed.

(** Invariant at positions where Maker [p] is to move. *)
Definition es_inv (p : player) (b : board_t) : Prop :=
  forall x, is_legal_move b x = true -> phi K b p lines + wgt K b p lines x < 2 ^ K.

Lemma breaker_choice : forall p b, (exists c, is_legal_move b c = true) ->
  exists c, is_legal_move b c = true /\
    forall y, is_legal_move b y = true -> wgt K b p lines y <= wgt K b p lines c.
Proof.
  intros p b [c0 Hc0].
  assert (Hne : legal_moves b <> []).
  { intros E. apply in_legal_moves in Hc0. rewrite E in Hc0. destruct Hc0. }
  destruct (argmax_in (wgt K b p lines) (legal_moves b) Hne) as [c [Hc Hmax]].
  exists c. split; [apply in_legal_moves; exact Hc |].
  intros y Hy. apply Hmax. apply in_legal_moves. exact Hy.
Qed.

(** Breaker's greedy reply never lets the potential grow. *)
Lemma breaker_reply_bound : forall p b c,
  is_legal_move b c = true ->
  (forall y, is_legal_move b y = true -> wgt K b p lines y <= wgt K b p lines c) ->
  forall y, is_legal_move (set_cell b c (other_player p)) y = true ->
  phi K (set_cell b c (other_player p)) p lines +
  wgt K (set_cell b c (other_player p)) p lines y <= phi K b p lines.
Proof.
  intros p b c Hc Hmax y Hy.
  pose proof (phi_breaker K b c p lines Hc) as E.
  pose proof (wgt_breaker_le K b c p lines y Hc) as Hle.
  pose proof (Hmax y (legal_after_set b c (other_player p) y Hc Hy)) as Hm.
  lia.
Qed.

Theorem erdos_selfridge_potential : forall p d b, es_inv p b -> ~ maker_wins lines p d b.
Proof.
  intros p d b Hinv H. revert Hinv.
  induction H as [d b m Hm Hw | d b m Hm Hex Hall IH]; intros Hinv.
  - apply check_win_iff in Hw as [L [HL Hown]].
    pose proof (Hinv m Hm) as Hlt.
    rewrite <- (phi_maker K b m p lines (fun L' HL' => proj1 (Hlines L' HL')) Hm) in Hlt.
    pose proof (phi_full K (set_cell b m p) p lines L HL
                  (proj2 (Hlines L HL)) Hown) as Hge.
    lia.
  - destruct (breaker_choice p (set_cell b m p) Hex) as [c [Hc Hmax]].
    apply (IH c Hc). intros y Hy.
    pose proof (breaker_reply_bound p (set_cell b m p) c Hc Hmax y Hy) as Hb.
    pose proof (Hinv m Hm) as Hlt.
    rewrite <- (phi_maker K b m p lines (fun L' HL' => proj1 (Hlines L' HL')) Hm) in Hlt.
    lia.
Qed.

(** Erdős–Selfridge, Breaker moving second:
    sum_L 2^(-|L|) < 1/2  ==>  Maker never claims a whole line. *)
Theorem erdos_selfridge_breaker_second : forall N p,
  2 * es_sum < 2 ^ K -> forall d, ~ maker_wins lines p d (empty_board N).
Proof.
  intros N p H d. apply erdos_selfridge_potential. intros x _.
  pose proof (wgt_le_phi K (empty_board N) p lines x) as Hw.
  rewrite phi_empty in Hw |- *. lia.
Qed.

(** Erdős–Selfridge, Breaker [p] moving first:
    sum_L 2^(-|L|) < 1  ==>  after Breaker's greedy opening, Maker never
    claims a whole line. *)
Theorem erdos_selfridge_breaker_first : forall N p,
  0 < N -> es_sum < 2 ^ K ->
  exists m, is_legal_move (empty_board N) m = true /\
    forall d, ~ maker_wins lines (other_player p) d (set_cell (empty_board N) m p).
Proof.
  intros N p HN H.
  assert (H0 : exists c, is_legal_move (empty_board N) c = true).
  { exists 0. apply legal_move_intro.
    - rewrite empty_board_length. exact HN.
    - apply get_cell_empty_board. }
  destruct (breaker_choice (other_player p) (empty_board N) H0) as [m [Hm Hmax]].
  exists m. split; [exact Hm |]. intros d.
  apply erdos_selfridge_potential. intros y Hy.
  pose proof (breaker_reply_bound (other_player p) (empty_board N) m Hm Hmax y) as Hb.
  rewrite other_player_involutive, phi_empty in Hb.
  specialize (Hb Hy). lia.
Qed.

(** Strong-game corollary: each player can play Breaker against the other,
    so neither can force a win. *)
Theorem erdos_selfridge_draw : forall N,
  2 * es_sum < 2 ^ K -> game_is_draw lines (empty_board N).
Proof.
  intros N H. split.
  - intros d Hf. apply (erdos_selfridge_breaker_second N P1 H d).
    apply forces_win_maker_wins. exact Hf.
  - intros d [[m0 Hm0] Hall].
    assert (HN : 0 < N).
    { apply legal_move_lt in Hm0. rewrite empty_board_length in Hm0. lia. }
    destruct (erdos_selfridge_breaker_first N P1 HN ltac:(lia)) as [m [Hm Hno]].
    destruct (Hall m Hm) as [_ Hf].
    apply (Hno d). apply forces_win_maker_wins. exact Hf.
Qed.

End ErdosSelfridge.

(* ========================================================================= *)
(** * 5. Consequences for (m, n, k) games                                    *)
(* ========================================================================= *)

Lemma es_sum_uniform : forall lines k,
  (forall L, In L lines -> length L = k) -> es_sum lines k = length lines.
Proof.
  intros lines k H. unfold es_sum. induction lines as [| L lines IH]; [reflexivity |].
  rewrite ls_cons. rewrite (H L (or_introl eq_refl)), Nat.sub_diag.
  simpl length. rewrite IH by (intros L' HL'; apply H; right; exact HL'). simpl. lia.
Qed.

(** If L(m, n, k) < 2^(k-1), the (m, n, k) game is a draw. *)
Theorem mnk_erdos_selfridge_draw : forall m n k,
  total_lines_formula m n k < 2 ^ (k - 1) ->
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof.
  intros m n k H.
  apply (erdos_selfridge_draw (gen_lines m n k) k).
  - intros L HL. split.
    + eapply gen_lines_nodup. exact HL.
    + rewrite (gen_lines_uniform m n k L HL). lia.
  - rewrite (es_sum_uniform (gen_lines m n k) k)
      by (intros L HL; eapply gen_lines_uniform; exact HL).
    rewrite gen_lines_count. destruct k as [| k'].
    + simpl in H |- *. lia.
    + replace (S k' - 1) with k' in H by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

Corollary mnk_prime_triple_11_7_7_draw :
  game_is_draw (gen_lines 11 7 7) (empty_board (11 * 7)).
Proof. apply mnk_erdos_selfridge_draw. exact mnk_prime_triple_11_7_7_erdos_bound. Qed.

Corollary mnk_prime_triple_17_13_11_draw :
  game_is_draw (gen_lines 17 13 11) (empty_board (17 * 13)).
Proof. apply mnk_erdos_selfridge_draw. exact mnk_prime_triple_17_13_11_erdos_bound. Qed.

Corollary mnk_prime_triple_19_17_13_draw :
  game_is_draw (gen_lines 19 17 13) (empty_board (19 * 17)).
Proof. apply mnk_erdos_selfridge_draw. exact mnk_prime_triple_19_17_13_erdos_bound. Qed.

(** Every near-square board with k >= 11 is a draw.  In particular every game
    (r, q, p) on consecutive primes p < q < r with p >= 11 is a draw, since
    r < 2p there (two primes in (p, 2p), Ramanujan 1919 - the number-theoretic
    input is cited, the game theory is formal). *)
Theorem mnk_near_square_draw : forall m n k,
  11 <= k -> k <= n -> k <= m -> n < 2 * k -> m < 2 * k ->
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof.
  intros m n k H1 H2 H3 H4 H5. apply mnk_erdos_selfridge_draw.
  apply erdos_selfridge_hypothesis_near_square; assumption.
Qed.

Lemma pow2_beats_linear : forall k, 5 <= k -> 2 * k + 2 < 2 ^ (k - 1).
Proof.
  intros k Hk. induction k as [| k IH]; [lia |].
  destruct (Nat.eq_dec k 4) as [-> | Hne]; [simpl; lia |].
  assert (H : 2 * k + 2 < 2 ^ (k - 1)) by (apply IH; lia).
  replace (S k - 1) with (S (k - 1)) by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

(** The square (k, k, k) game is a draw for every k >= 5. *)
Theorem mnk_square_k_draw : forall k, 5 <= k ->
  game_is_draw (gen_lines k k k) (empty_board (k * k)).
Proof.
  intros k Hk. apply mnk_erdos_selfridge_draw.
  assert (E : total_lines_formula k k k = 2 * k + 2).
  { unfold total_lines_formula, horiz_lines_count, vert_lines_count,
      diag1_lines_count, diag2_lines_count.
    rewrite Nat.leb_refl. simpl. rewrite !Nat.sub_diag. lia. }
  rewrite E. apply pow2_beats_linear. exact Hk.
Qed.
