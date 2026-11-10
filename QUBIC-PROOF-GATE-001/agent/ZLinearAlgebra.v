(** Binary line codes and information-set certificates. All algebra is proved
    here over N.lxor; no external rank computation is trusted. *)
From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
Import ListNotations.

Definition bit (word : N) (c : cell) : bool := N.testbit word (N.of_nat c).
Definition zero_on (word : N) (cells : list cell) : Prop :=
  forall c, In c cells -> bit word c = false.
Definition zero_onb (word : N) (cells : list cell) : bool :=
  forallb (fun c => negb (bit word c)) cells.
Definition zero_board (word : N) : Prop := forall c, c < 125 -> bit word c = false.
Definition nonzero_board (word : N) : Prop := exists c, c < 125 /\ bit word c = true.

Lemma bit_xor : forall u v c,
  bit (N.lxor u v) c = xorb (bit u c) (bit v c).
Proof. intros. apply N.lxor_spec. Qed.

Lemma bit_zero : forall c, bit 0%N c = false.
Proof. intros c. unfold bit. destruct (N.of_nat c); reflexivity. Qed.

Lemma xor_swap : forall a b c,
  N.lxor a (N.lxor b c) = N.lxor b (N.lxor a c).
Proof.
  intros. apply N.bits_inj. intros n. rewrite !N.lxor_spec.
  destruct (N.testbit a n), (N.testbit b n), (N.testbit c n); reflexivity.
Qed.

Lemma xor_cancel : forall a b c,
  N.lxor (N.lxor a b) (N.lxor a c) = N.lxor b c.
Proof.
  intros. apply N.bits_inj. intros n. rewrite !N.lxor_spec.
  destruct (N.testbit a n), (N.testbit b n), (N.testbit c n); reflexivity.
Qed.

Fixpoint code_words (rows : list N) : list N :=
  match rows with
  | [] => [0%N]
  | row :: rest => code_words rest ++ map (N.lxor row) (code_words rest)
  end.

Definition xor_closed (code : list N) : Prop :=
  forall u v, In u code -> In v code -> In (N.lxor u v) code.

Lemma code_words_closed : forall rows, xor_closed (code_words rows).
Proof.
  intros rows. induction rows as [|row rows IH]; intros u v Hu Hv.
  - destruct Hu as [Hu|Hu], Hv as [Hv|Hv]; try contradiction.
    subst u v. left. reflexivity.
  - change (In u (code_words rows ++ map (N.lxor row) (code_words rows))) in Hu.
    change (In v (code_words rows ++ map (N.lxor row) (code_words rows))) in Hv.
    change (In (N.lxor u v) (code_words rows ++ map (N.lxor row) (code_words rows))).
    apply in_app_iff in Hu as [Hu|Hu]; apply in_app_iff in Hv as [Hv|Hv].
    + apply in_app_iff. left. apply IH; assumption.
    + apply in_map_iff in Hv as [w [<- Hw]]. rewrite xor_swap.
      apply in_app_iff. right. apply in_map, IH; assumption.
    + apply in_map_iff in Hu as [w [<- Hw]]. rewrite N.lxor_assoc.
      apply in_app_iff. right. apply in_map, IH; assumption.
    + apply in_map_iff in Hu as [a [<- Ha]]. apply in_map_iff in Hv as [b [<- Hb]].
      rewrite xor_cancel. apply in_app_iff. left. apply IH; assumption.
Qed.

Lemma zero_in_code_words : forall rows, In 0%N (code_words rows).
Proof.
  induction rows as [|row rows IH]; [left; reflexivity|].
  apply in_app_iff. left. exact IH.
Qed.

Lemma generator_in_code_words : forall rows row,
  In row rows -> In row (code_words rows).
Proof.
  induction rows as [|head rows IH]; intros row Hin; [contradiction|].
  apply in_app_iff. destruct Hin as [<-|Hin].
  - right. apply in_map_iff. exists 0%N. split; [apply N.lxor_0_r|apply zero_in_code_words].
  - left. apply IH. exact Hin.
Qed.

Definition Decoder := list (cell * N).
Definition decoder_cells (decoder : Decoder) : list cell := map fst decoder.

Fixpoint reconstruct (decoder : Decoder) (word : N) : N :=
  match decoder with
  | [] => 0%N
  | (c, decoded) :: rest =>
      if bit word c then N.lxor decoded (reconstruct rest word) else reconstruct rest word
  end.

Lemma reconstruct_linear : forall decoder u v,
  reconstruct decoder (N.lxor u v) = N.lxor (reconstruct decoder u) (reconstruct decoder v).
Proof.
  induction decoder as [|[c decoded] rest IH]; intros u v; [reflexivity|].
  cbn [reconstruct]. rewrite bit_xor, IH.
  destruct (bit u c), (bit v c); cbn.
  - symmetry. apply xor_cancel.
  - symmetry. apply N.lxor_assoc.
  - apply xor_swap.
  - reflexivity.
Qed.

Lemma reconstruct_code_word : forall rows decoder,
  (forall row, In row rows -> reconstruct decoder row = row) ->
  forall word, In word (code_words rows) -> reconstruct decoder word = word.
Proof.
  induction rows as [|row rows IH]; intros decoder Hrows word Hin.
  - destruct Hin as [<-|Hin]; [|contradiction].
    clear Hrows. induction decoder as [|[c d] rest IHd]; [reflexivity|].
    cbn [reconstruct]. rewrite bit_zero. exact IHd.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply IH; [intros r Hr; apply Hrows; right; exact Hr|exact Hin].
    + apply in_map_iff in Hin as [w [<- Hw]]. rewrite reconstruct_linear.
      rewrite Hrows by (left; reflexivity).
      assert (Hword : reconstruct decoder w = w).
      { apply IH; [intros r Hr; apply Hrows; right; exact Hr|exact Hw]. }
      rewrite Hword. reflexivity.
Qed.

Lemma reconstruct_zero_on : forall decoder word,
  zero_on word (decoder_cells decoder) -> reconstruct decoder word = 0%N.
Proof.
  induction decoder as [|[c d] rest IH]; intros word Hzero; [reflexivity|].
  cbn [reconstruct]. rewrite Hzero by (left; reflexivity). apply IH.
  intros p Hp. apply Hzero. right. exact Hp.
Qed.

Lemma decoder_detects : forall rows decoder,
  (forall row, In row rows -> reconstruct decoder row = row) ->
  forall word, In word (code_words rows) -> zero_on word (decoder_cells decoder) -> zero_board word.
Proof.
  intros rows decoder Hrows word Hin Hzero.
  pose proof (reconstruct_code_word rows decoder Hrows word Hin) as Hid.
  pose proof (reconstruct_zero_on decoder word Hzero) as HzeroN.
  assert (Hword : word = 0%N) by congruence. subst word. intros c Hc. apply bit_zero.
Qed.

Lemma zero_onb_spec : forall word cells,
  zero_onb word cells = true <-> zero_on word cells.
Proof.
  intros word cells. unfold zero_onb, zero_on. rewrite forallb_forall.
  split; intros H c Hc; specialize (H c Hc); apply negb_true_iff in H || apply negb_true_iff; exact H.
Qed.

Lemma zero_on_xor : forall u v cells,
  zero_on u cells -> zero_on v cells -> zero_on (N.lxor u v) cells.
Proof. intros u v cells Hu Hv c Hc. rewrite bit_xor, Hu, Hv by exact Hc. reflexivity. Qed.

Lemma zero_on_extend_removed : forall word cells removed,
  zero_on word (remove Nat.eq_dec removed cells) -> bit word removed = false -> zero_on word cells.
Proof.
  intros word cells removed Hzero Hremoved c Hc.
  destruct (Nat.eq_dec c removed) as [->|Hneq]; [exact Hremoved|].
  apply Hzero, in_in_remove; assumption.
Qed.

Lemma zero_on_shrink : forall word small large,
  incl small large -> zero_on word large -> zero_on word small.
Proof. intros word small large Hi Hz c Hc. apply Hz, Hi. exact Hc. Qed.

Print Assumptions code_words_closed.
Print Assumptions decoder_detects.
