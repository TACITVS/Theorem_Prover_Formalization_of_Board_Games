(** A universal capacity theorem for every well-mated static pair defense,
    not merely a numerical inequality for one proposed schedule. *)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Geometry Minimax RulesFacts SafePairing Tactics.
Import ListNotations.

Definition unblocked_lines (st : GameState) : list (list cell) :=
  filter (fun l => negb (existsb (fun c => existsb (Nat.eqb c) (black_stones st)) l)) all_lines.
Definition empty_cells (st : GameState) : list cell := filter (is_legal_move st) all_cells.
Definition chosen_pair (mate : mate_function) (l : list cell) : list cell :=
  match find (fun c => negb (mate c =? c) && existsb (Nat.eqb (mate c)) l) l with
  | Some c => [c; mate c]
  | None => []
  end.

Local Opaque all_lines.

Lemma unblocked_properties : forall st l,
  In l (unblocked_lines st) -> In l all_lines /\
  (forall c, In c l -> ~ In c (black_stones st)).
Proof.
  intros st l H. apply filter_In in H as [Hl Hfree].
  apply negb_true_iff in Hfree. split; [exact Hl|].
  intros c Hcl Hcb.
  assert (Hbad : existsb (fun c => existsb (Nat.eqb c) (black_stones st)) l = true).
  { apply existsb_exists. exists c. split; [exact Hcl|apply member_spec; exact Hcb]. }
  congruence.
Qed.

Lemma chosen_pair_exists : forall st mate l,
  pairing_safe mate st -> In l (unblocked_lines st) ->
  exists a, find (fun c => negb (mate c =? c) && existsb (Nat.eqb (mate c)) l) l = Some a.
Proof.
  intros st mate l [_ Hcover] Hin.
  destruct (unblocked_properties st l Hin) as [Hl Hnot].
  destruct (Hcover l Hl) as [[c [Hc Hcb]]|[c [Hc [Hmc Hneq]]]].
  - exfalso. apply (Hnot c Hc). exact Hcb.
  - destruct (find (fun c => negb (mate c =? c) && existsb (Nat.eqb (mate c)) l) l) eqn:Hfind;
      [eauto|].
    pose proof (@find_none cell _ _ Hfind c Hc) as Hnone.
    assert (Hyes : negb (mate c =? c) && existsb (Nat.eqb (mate c)) l = true).
    { apply andb_true_iff. split; [apply negb_true_iff, Nat.eqb_neq; exact Hneq|apply member_spec; exact Hmc]. }
    cbn beta in Hnone. congruence.
Qed.

Lemma chosen_pair_facts : forall st mate l,
  well_mated mate -> pairing_safe mate st -> In l (unblocked_lines st) ->
  length (chosen_pair mate l) = 2 /\ NoDup (chosen_pair mate l) /\
  (forall c, In c (chosen_pair mate l) ->
    In c l /\ is_legal_move st c = true /\ In (mate c) (chosen_pair mate l) /\ mate c <> c).
Proof.
  intros st mate l Hmate Hsafe Hl.
  destruct (chosen_pair_exists st mate l Hsafe Hl) as [a Hfind].
  pose proof Hfind as Hfound. apply find_some in Hfound as [Ha Hpred].
  apply andb_true_iff in Hpred as [Hneq Hma].
  apply negb_true_iff, Nat.eqb_neq in Hneq. apply member_spec in Hma.
  destruct (unblocked_properties st l Hl) as [Hline HnotB].
  assert (Ha_bound : a < 125) by (eapply locked_line_cell_bound; eassumption).
  destruct (Hmate a Ha_bound) as [Hma_bound Hinv].
  destruct Hsafe as [Hresponse Hcover].
  assert (HnotWa : ~ In a (white_stones st)).
  { intros Hw. apply (HnotB (mate a) Hma), Hresponse; assumption. }
  assert (HnotWma : ~ In (mate a) (white_stones st)).
  { intros Hw. assert (Hneq' : mate (mate a) <> mate a) by congruence.
    pose proof (Hresponse _ Hma_bound Hneq' Hw) as Hb. rewrite Hinv in Hb.
    apply (HnotB a Ha). exact Hb. }
  assert (Hlegal : forall c, In c l -> ~ In c (white_stones st) -> is_legal_move st c = true).
  { intros c Hc HnotW. unfold is_legal_move. apply andb_true_iff. split.
    - apply Nat.ltb_lt. eapply locked_line_cell_bound; eassumption.
    - apply negb_true_iff. destruct (occupied st c) eqn:Hocc; [|reflexivity].
      apply occupied_spec in Hocc. apply in_app_iff in Hocc as [Hw|Hb]; contradiction || (exfalso; apply (HnotB c Hc); exact Hb). }
  unfold chosen_pair. rewrite Hfind. split; [reflexivity|]. split.
  - constructor; [intros [Heq|H]; [congruence|contradiction]|].
    constructor; [intros H; contradiction|constructor].
  - intros c [Hc|[Hc|Hc]]; [subst c|subst c|contradiction].
    + repeat split; try assumption; [apply Hlegal; assumption|right; left; reflexivity].
    + rewrite Hinv. repeat split; try assumption.
      * apply Hlegal; assumption.
      * left. reflexivity.
      * congruence.
Qed.

Lemma chosen_pairs_disjoint : forall st mate a b,
  well_mated mate -> pairing_safe mate st ->
  In a (unblocked_lines st) -> In b (unblocked_lines st) -> a <> b ->
  forall c, In c (chosen_pair mate a) -> ~ In c (chosen_pair mate b).
Proof.
  intros st mate a b Hmate Hsafe Ha Hb Hneq c Hca Hcb.
  destruct (chosen_pair_facts st mate a Hmate Hsafe Ha) as [_ [_ Hpa]].
  destruct (chosen_pair_facts st mate b Hmate Hsafe Hb) as [_ [_ Hpb]].
  destruct (Hpa c Hca) as [Hca' [_ [Hmca Hmcneq]]].
  destruct (Hpb c Hcb) as [Hcb' _].
  destruct (Hpa (mate c) Hmca) as [Hmca' _].
  destruct (Hpb c Hcb) as [_ [_ [Hmcb _]]].
  destruct (Hpb (mate c) Hmcb) as [Hmcb' _].
  destruct (unblocked_properties st a Ha) as [Hla _].
  destruct (unblocked_properties st b Hb) as [Hlb _].
  pose proof (winning_lines_linear a b Hla Hlb Hneq) as Hlinear.
  assert (Hnd : NoDup [c; mate c]).
  { constructor; [intros [Heq|H]; [congruence|contradiction]|].
    constructor; [intros H; contradiction|constructor]. }
  assert (Hinc : incl [c; mate c] (intersection a b)).
  { intros d [Hd|[Hd|Hd]]; [subst d|subst d|contradiction];
      apply filter_In; split; try assumption; apply member_spec; assumption. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hbound. cbn in Hbound. lia.
Qed.

Lemma flat_pairs_nodup : forall (pairs : list cell -> list cell) lines,
  NoDup lines -> (forall l, In l lines -> NoDup (pairs l)) ->
  (forall a b, In a lines -> In b lines -> a <> b -> forall c, In c (pairs a) -> ~ In c (pairs b)) ->
  NoDup (flat_map pairs lines).
Proof.
  intros pairs lines. induction lines as [|l lines IH]; intros Hnd Hpair Hdis; [constructor|].
  inversion Hnd as [|? ? Hnot Htail]; subst. cbn. apply NoDup_app.
  - apply Hpair. left. reflexivity.
  - apply IH; [exact Htail|intros; apply Hpair; right; assumption|].
    intros a b Ha Hb Hneq c Hca Hcb.
    exact (Hdis a b (or_intror Ha) (or_intror Hb) Hneq c Hca Hcb).
  - intros c Hc Hin. apply in_flat_map in Hin as [other [Ho Hco]].
    assert (Hneq : l <> other) by (intro Heq; subst other; contradiction).
    exact (Hdis l other (or_introl eq_refl) (or_intror Ho) Hneq c Hc Hco).
Qed.

Lemma flat_pairs_length : forall (pairs : list cell -> list cell) lines,
  (forall l, In l lines -> length (pairs l) = 2) ->
  length (flat_map pairs lines) = 2 * length lines.
Proof.
  intros pairs lines. induction lines as [|l lines IH]; intros H; [reflexivity|].
  cbn [flat_map]. rewrite length_app, H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption). cbn. lia.
Qed.

Theorem every_static_pairing_needs_capacity : forall st mate,
  well_mated mate -> pairing_safe mate st ->
  2 * length (unblocked_lines st) <= length (empty_cells st).
Proof.
  intros st mate Hmate Hsafe.
  assert (Hnd : NoDup (flat_map (chosen_pair mate) (unblocked_lines st))).
  { apply flat_pairs_nodup.
    - apply NoDup_filter, locked_lines_distinct.
    - intros l Hl. exact (proj1 (proj2 (chosen_pair_facts st mate l Hmate Hsafe Hl))).
    - intros a b Ha Hb Hneq. apply chosen_pairs_disjoint with (st := st); assumption. }
  assert (Hinc : incl (flat_map (chosen_pair mate) (unblocked_lines st)) (empty_cells st)).
  { intros c Hin. apply in_flat_map in Hin as [l [Hl Hc]].
    destruct (chosen_pair_facts st mate l Hmate Hsafe Hl) as [_ [_ Hprops]].
    destruct (Hprops c Hc) as [Hcl [Hlegal _]].
    apply filter_In. split; [apply in_seq; destruct (legal_move_fresh st c Hlegal); lia|exact Hlegal]. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hbound.
  rewrite flat_pairs_length in Hbound; [exact Hbound|].
  intros l Hl. exact (proj1 (chosen_pair_facts st mate l Hmate Hsafe Hl)).
Qed.

Print Assumptions every_static_pairing_needs_capacity.
