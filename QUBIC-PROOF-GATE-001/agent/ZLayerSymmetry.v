(** The same permutation of the five levels on all three axes exchanges
    inner and outer layers and commutes with coordinate reversal. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Geometry Minimax SymmetryGame.
Import ListNotations.

Definition layer n := match n with 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | _ => 3 end.
Definition exchange_layers c :=
  layer (coord_x c) + 5 * layer (coord_y c) + 25 * layer (coord_z c).

Definition reorder (l : list cell) :=
  match l with [a;b;c;d;e] => [b;a;c;e;d] | _ => l end.
Lemma reorder_perm : forall l, Permutation l (reorder l).
Proof.
  intros [|a [|b [|c [|d [|e [|f t]]]]]]; try reflexivity.
  cbn. eapply Permutation_trans; [apply perm_swap|].
  do 3 apply perm_skip. apply perm_swap.
Qed.

Definition image_ok l :=
  let m := map exchange_layers l in
  contains_line m oriented_lines || contains_line (reorder m) oriented_lines.
Lemma all_images_ok : forallb image_ok all_lines = true.
Proof. vm_compute. reflexivity. Qed.
Lemma layer_images : forall l, In l all_lines ->
  exists k, In k all_lines /\ Permutation (map exchange_layers l) k.
Proof.
  intros l Hl. pose proof all_images_ok as H.
  apply forallb_forall with (x:=l) in H; auto.
  unfold image_ok in H. apply orb_true_iff in H as [H|H];
  apply contains_line_spec, oriented_lines_spec in H; destruct H as [H|H];
  eexists; split; try exact H.
  - reflexivity.
  - apply Permutation_rev.
  - apply reorder_perm.
  - eapply Permutation_trans; [apply reorder_perm|apply Permutation_rev].
Qed.

Lemma layer_cells : forall c, c < 125 ->
  exchange_layers c < 125 /\ exchange_layers (exchange_layers c) = c.
Proof.
  assert (H : forallb (fun c => (exchange_layers c <? 125) &&
    (exchange_layers (exchange_layers c) =? c)) all_cells = true) by (vm_compute; reflexivity).
  intros c Hc. apply forallb_forall with (x:=c) in H; [|apply in_seq; lia].
  apply andb_true_iff in H as [Ha Hb]. apply Nat.ltb_lt in Ha. apply Nat.eqb_eq in Hb. auto.
Qed.
Definition layer_iso : BoardIso.
Proof.
  refine {| forward := exchange_layers; backward := exchange_layers |};
    try exact layer_images; intros c Hc; apply layer_cells; assumption.
Defined.

Definition six : list cell := [0;1;2;7;12;62].
Definition actions := cube_symmetries ++ map (compose_iso layer_iso) cube_symmetries.
Lemma six_cover : forall c, c < 125 ->
  exists iso, forward iso 62 = 62 /\ In (forward iso c) six.
Proof.
  assert (H : forallb (fun c => existsb (fun iso =>
    existsb (Nat.eqb (forward iso c)) six) actions) all_cells = true) by (vm_compute; reflexivity).
  intros c Hc. apply forallb_forall with (x:=c) in H; [|apply in_seq; lia].
  apply existsb_exists in H as [iso [Hin H]]. exists iso. split.
  { assert (F : forallb (fun i => forward i 62 =? 62) actions = true) by (vm_compute; reflexivity).
    apply forallb_forall with (x:=iso) in F; [apply Nat.eqb_eq; exact F|exact Hin]. }
  apply existsb_exists in H as [y [Hy E]]. apply Nat.eqb_eq in E. rewrite E. exact Hy.
Qed.

Theorem exact_draw_iff_six_openings :
  Goal.ExactDraw <-> forall c, In c six -> opening_nonloss c.
Proof.
  rewrite Stealing.exact_draw_iff_black_nonloss, black_nonloss_iff_all_openings.
  split.
  - intros H c Hc. apply H. unfold six in Hc. simpl in Hc. lia.
  - intros H c Hc. destruct (six_cover c Hc) as [iso [_ Hi]].
    specialize (H _ Hi). unfold opening_nonloss in *.
    pose proof (solve_symmetry iso prevents_white false 124 false (opening_state c)
      (opening_valid c Hc) eq_refl) as Heq.
    change (solve prevents_white false 124 false (opening_state (forward iso c)) =
      solve prevents_white false 124 false (opening_state c)) in Heq.
    congruence.
Qed.
Print Assumptions exact_draw_iff_six_openings.

Local Opaque solve.
Definition center_replies := [0;1;2;7;12].
Definition center_reply_value :=
  branch prevents_white (solve prevents_white false 123) false (opening_state 62).

Theorem center_opening_iff_five_replies :
  opening_nonloss 62 <-> exists c, In c center_replies /\ center_reply_value c = true.
Proof.
  unfold opening_nonloss. rewrite Stealing.solve_successor.
  change (existsb center_reply_value requests = true <-> exists c, In c center_replies /\ center_reply_value c = true).
  rewrite existsb_exists. split.
  - intros [r [_ Hr]]. set (st := opening_state 62) in *.
    assert (Hv : RulesFacts.valid_state st) by (apply opening_valid; lia).
    set (x := effective_move st r).
    assert (Hx : is_legal_move st x = true) by
      (apply RulesFacts.effective_move_is_legal; [exact Hv|unfold st; cbn; lia]).
    destruct (SafePairing.legal_move_fresh _ _ Hx) as [Hbound [Hw _]].
    assert (Hdiff : x <> 62) by (intro E; apply Hw; rewrite E; left; reflexivity).
    destruct (six_cover x Hbound) as [iso [Hfix Hin]].
    exists (forward iso x). split.
    + assert (Hneq : forward iso x <> 62).
      { intro E. apply Hdiff. apply (forward_injective iso); lia. }
      unfold six in Hin. unfold center_replies. simpl in Hin |- *. tauto || intuition congruence.
    + pose proof (branch_transport iso prevents_white false 123 false st r
        (fun next => solve_symmetry iso prevents_white false 123 true next) Hv eq_refl) as H.
      assert (E : transport iso st = st).
      { unfold st, transport, opening_state. cbn. rewrite Hfix. reflexivity. }
      rewrite E in H. unfold center_reply_value in *. exact (eq_trans H Hr).
  - intros [c [Hc H]]. exists c. split; [|exact H].
    apply in_seq. unfold center_replies in Hc. simpl in Hc. lia.
Qed.
Print Assumptions center_opening_iff_five_replies.
