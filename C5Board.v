(** * Basic facts about boards, moves and gravity *)
From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
From C5 Require Import C5Game.

Lemma peqb_eq : forall p q, peqb p q = true <-> p = q.
Proof. intros [] []; simpl; split; congruence. Qed.

Lemma other_neq : forall p, other p <> p.
Proof. intros []; discriminate. Qed.

Lemma other_other : forall p, other (other p) = p.
Proof. intros []; reflexivity. Qed.

Lemma player_dec : forall p q : player, {p = q} + {p <> q}.
Proof. decide equality. Qed.

(** Well-formed boards: 8 columns of height at most 8. *)
Definition wf (b : board) : Prop :=
  length b = 8 /\ forall c, length (col b c) <= 8.

Lemma length_replace : forall (A : Type) (l : list A) n v,
  length (replace l n v) = length l.
Proof. induction l; intros [|n] v; simpl; auto. Qed.

Lemma nth_replace : forall (A : Type) (l : list A) n v m dflt,
  n < length l ->
  nth m (replace l n v) dflt = if m =? n then v else nth m l dflt.
Proof.
  induction l as [|h t IH]; intros n v m dflt Hn; simpl in *; [lia|].
  destruct n as [|n], m as [|m]; simpl; auto.
  apply IH; lia.
Qed.

Lemma legal_spec : forall b c,
  legal b c = true <-> c < 8 /\ length (col b c) < 8.
Proof.
  intros b c; unfold legal.
  rewrite andb_true_iff, !Nat.ltb_lt; tauto.
Qed.

Lemma col_play : forall b c p c',
  wf b -> c < 8 ->
  col (play b c p) c' = if c' =? c then col b c ++ [p] else col b c'.
Proof.
  intros b c p c' [Hl _] Hc; unfold col, play.
  rewrite nth_replace by lia; reflexivity.
Qed.

Lemma wf_play : forall b c p,
  wf b -> legal b c = true -> wf (play b c p).
Proof.
  intros b c p Hwf Hleg.
  pose proof Hleg as Hl'. apply legal_spec in Hl' as [Hc Hlen].
  split.
  - unfold play; rewrite length_replace; exact (proj1 Hwf).
  - intros c'. rewrite col_play by assumption.
    destruct (c' =? c) eqn:E.
    + apply Nat.eqb_eq in E; subst c'. rewrite length_app; simpl; lia.
    + apply (proj2 Hwf).
Qed.

Lemma owner_None : forall b c r,
  owner b (c, r) = None <-> length (col b c) <= r.
Proof. intros; unfold owner; simpl; apply nth_error_None. Qed.

Lemma owner_Some_lt : forall b c r p,
  owner b (c, r) = Some p -> r < length (col b c).
Proof.
  intros b c r p H.
  destruct (Nat.lt_ge_cases r (length (col b c))) as [|Hge]; auto.
  apply owner_None in Hge. congruence.
Qed.

Lemma owner_play : forall b c p x,
  wf b -> legal b c = true ->
  owner (play b c p) x =
    if (fst x =? c) && (snd x =? length (col b c)) then Some p else owner b x.
Proof.
  intros b c p [xc xr] Hwf Hleg.
  pose proof Hleg as Hl. apply legal_spec in Hl as [Hc Hlen].
  unfold owner; simpl. rewrite col_play by auto.
  destruct (xc =? c) eqn:E; simpl.
  - apply Nat.eqb_eq in E; subst xc.
    destruct (xr =? length (col b c)) eqn:F.
    + apply Nat.eqb_eq in F; subst xr.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + apply Nat.eqb_neq in F.
      destruct (Nat.lt_ge_cases xr (length (col b c))) as [Hlt|Hge].
      * rewrite nth_error_app1 by lia. reflexivity.
      * rewrite nth_error_app2 by lia.
        assert (Hx: nth_error (col b c) xr = None) by (apply nth_error_None; lia).
        rewrite Hx. destruct (xr - length (col b c)) eqn:G; [lia|].
        simpl. destruct n; reflexivity.
  - reflexivity.
Qed.

(** The cell where a move in column [c] lands. *)
Definition landing (b : board) (c : nat) : cell := (c, length (col b c)).

Lemma owner_play_landing : forall b c p,
  wf b -> legal b c = true -> owner (play b c p) (landing b c) = Some p.
Proof.
  intros. rewrite owner_play by auto. unfold landing; simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma owner_play_other : forall b c p x,
  wf b -> legal b c = true -> x <> landing b c ->
  owner (play b c p) x = owner b x.
Proof.
  intros b c p [xc xr] Hwf Hleg Hne. rewrite owner_play by auto. simpl.
  destruct (xc =? c) eqn:E1, (xr =? length (col b c)) eqn:E2; simpl; auto.
  apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2; subst.
  exfalso; apply Hne; reflexivity.
Qed.

Lemma landing_empty : forall b c, owner b (landing b c) = None.
Proof. intros; unfold landing; apply owner_None; lia. Qed.

Lemma forallb_false_ex : forall (A : Type) (f : A -> bool) (l : list A),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  induction l as [|a l IH]; simpl; intros H; [discriminate|].
  destruct (f a) eqn:E; simpl in H.
  - destruct (IH H) as [x [Hx Hf]]; eauto.
  - eauto.
Qed.

Lemma full_false_iff : forall b,
  full b = false <-> exists c, legal b c = true.
Proof.
  intros b; unfold full; split.
  - intros H. apply forallb_false_ex in H as [c [_ Hc]].
    exists c. destruct (legal b c); auto.
  - intros [c Hc]. apply Bool.not_true_iff_false. intros H.
    pose proof Hc as Hc'. apply legal_spec in Hc' as [Hlt _].
    rewrite forallb_forall in H.
    specialize (H c). rewrite Hc in H. simpl in H.
    assert (In c (seq 0 8)) by (apply in_seq; lia).
    specialize (H H0). discriminate.
Qed.

Lemma wf_initial : wf initial.
Proof.
  split; [reflexivity|].
  intros c; unfold col, initial.
  destruct (Nat.lt_ge_cases c 8).
  - rewrite nth_repeat_lt by lia. simpl; lia.
  - rewrite nth_overflow by (rewrite repeat_length; lia). simpl; lia.
Qed.

(** ** Number of empty cells *)
Definition empties (b : board) : nat :=
  list_sum (map (fun c => 8 - length (col b c)) (seq 0 8)).

Lemma sum_change : forall (l : list nat) (c : nat) (f g : nat -> nat),
  NoDup l -> In c l ->
  (forall x, x <> c -> f x = g x) -> f c = S (g c) ->
  list_sum (map f l) = S (list_sum (map g l)).
Proof.
  induction l as [|h t IH]; intros c f g Hnd Hin Hfg Hc; [destruct Hin|].
  inversion Hnd as [|? ? Hnot Hnd']; subst.
  simpl. destruct Hin as [->|Hin].
  - rewrite Hc.
    assert (map f t = map g t) as ->.
    { apply map_ext_in. intros x Hx. apply Hfg. intros ->. contradiction. }
    lia.
  - rewrite (IH c f g) by auto.
    rewrite Hfg by (intros ->; contradiction). lia.
Qed.

Lemma empties_play : forall b c p,
  wf b -> legal b c = true -> S (empties (play b c p)) = empties b.
Proof.
  intros b c p Hwf Hleg.
  pose proof Hleg as Hl. apply legal_spec in Hl as [Hc Hlen].
  unfold empties. symmetry.
  apply sum_change with (c := c).
  - apply seq_NoDup.
  - apply in_seq; lia.
  - intros x Hx. rewrite col_play by auto.
    apply Nat.eqb_neq in Hx. rewrite Hx. reflexivity.
  - cbv beta. rewrite col_play by auto. rewrite Nat.eqb_refl, length_app.
    change (length [p]) with 1. lia.
Qed.

(** ** Monotonicity: discs are never removed *)
Definition extends (b b' : board) : Prop :=
  forall x, owner b x <> None -> owner b' x = owner b x.

Lemma extends_refl : forall b, extends b b.
Proof. intros b x _; reflexivity. Qed.

Lemma extends_play : forall b b' c p,
  wf b' -> legal b' c = true -> extends b b' -> extends b (play b' c p).
Proof.
  intros b b' c p Hwf Hleg Hext x Hx.
  assert (Hne : x <> landing b' c).
  { intros ->. pose proof (landing_empty b' c) as He.
    rewrite (Hext _ Hx) in He. contradiction. }
  rewrite owner_play_other by auto. apply Hext; auto.
Qed.

Lemma extends_length : forall b b' c,
  extends b b' -> length (col b c) <= length (col b' c).
Proof.
  intros b b' c Hext.
  destruct (Nat.le_gt_cases (length (col b c)) (length (col b' c))) as [|Hgt]; auto.
  exfalso.
  assert (H1 : owner b (c, length (col b' c)) <> None).
  { intros Hn. apply owner_None in Hn. lia. }
  pose proof (Hext _ H1) as H2.
  assert (H3 : owner b' (c, length (col b' c)) = None) by (apply owner_None; lia).
  congruence.
Qed.

Lemma extends_empty : forall b b' x,
  extends b b' -> owner b' x = None -> owner b x = None.
Proof.
  intros b b' x Hext H.
  destruct (owner b x) eqn:E; [|reflexivity].
  exfalso. assert (Hn : owner b x <> None) by congruence.
  specialize (Hext x Hn). rewrite E in Hext. congruence.
Qed.

Lemma has_line_false : forall b p,
  (forall L, In L lines -> exists x, In x L /\ owned_by b p x = false) ->
  has_line b p = false.
Proof.
  intros b p H. unfold has_line.
  apply Bool.not_true_iff_false. intros Hc.
  apply existsb_exists in Hc as [L [HL Hall]].
  destruct (H L HL) as [x [Hx Hf]].
  rewrite forallb_forall in Hall. rewrite Hall in Hf by auto. discriminate.
Qed.

Lemma has_line_true : forall b p L,
  In L lines -> (forall x, In x L -> owner b x = Some p) -> has_line b p = true.
Proof.
  intros b p L HL Hall. unfold has_line. apply existsb_exists.
  exists L; split; auto. apply forallb_forall. intros x Hx.
  unfold owned_by. rewrite (Hall x Hx). apply peqb_eq; reflexivity.
Qed.

Lemma owned_by_false : forall b p x,
  owner b x <> Some p -> owned_by b p x = false.
Proof.
  intros b p x H. unfold owned_by.
  destruct (owner b x) as [q|]; auto.
  destruct (peqb q p) eqn:E; auto. apply peqb_eq in E; subst; contradiction.
Qed.
