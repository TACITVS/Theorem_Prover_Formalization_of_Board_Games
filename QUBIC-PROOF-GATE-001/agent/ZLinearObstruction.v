(** Exact obstruction to the whole-line binary code at the empty board. *)
From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import ZLinearAlgebra ZLinearDefense.
Import ListNotations.

Definition whole_line_rows := map word_of_cells all_lines.
Definition center_indices : list nat :=
  [2;10;14;22;27;36;37;38;47;57;61;63;67;79;80;89;90;99;100].
Definition center_rows := map (fun i => nth i whole_line_rows 0%N) center_indices.
Fixpoint xor_rows (rows : list N) : N :=
  match rows with [] => 0%N | row :: rest => N.lxor row (xor_rows rest) end.
Definition center_word := word_of_cells [62].

Theorem nineteen_lines_isolate_center : xor_rows center_rows = center_word.
Proof. vm_compute. reflexivity. Qed.

Lemma center_rows_are_generators : forall row,
  In row center_rows -> In row whole_line_rows.
Proof.
  assert (H : forallb (fun row => existsb (N.eqb row) whole_line_rows) center_rows = true)
    by (vm_compute; reflexivity).
  intros row Hin. apply forallb_forall with (x:=row) in H; [|exact Hin].
  apply existsb_exists in H as [r [Hr E]]. apply N.eqb_eq in E. congruence.
Qed.

Lemma xor_generators_in_code : forall rows selected,
  incl selected rows -> In (xor_rows selected) (code_words rows).
Proof.
  intros rows selected. induction selected as [|row rest IH]; intros Hinc.
  - apply zero_in_code_words.
  - cbn [xor_rows]. apply code_words_closed.
    + apply generator_in_code_words, Hinc. left. reflexivity.
    + apply IH. intros r Hr. apply Hinc. right. exact Hr.
Qed.

Theorem center_is_in_whole_line_code : In center_word (code_words whole_line_rows).
Proof.
  rewrite <- nineteen_lines_isolate_center. apply xor_generators_in_code.
  exact center_rows_are_generators.
Qed.

Lemma singleton_zero_away_from_center : forall reserve,
  ~ In 62 reserve -> zero_on center_word reserve.
Proof.
  intros reserve Hnot c Hc. destruct (bit center_word c) eqn:Hbit; [|reflexivity].
  unfold center_word in Hbit. apply bit_word_of_cells in Hbit.
  destruct Hbit as [E|E]; [subst c; contradiction|contradiction].
Qed.

Theorem whole_line_information_requires_center : forall reserve,
  information (code_words whole_line_rows) [] reserve -> In 62 reserve.
Proof.
  intros reserve Hinfo. destruct (in_dec Nat.eq_dec 62 reserve); [assumption|].
  assert (Hz : zero_board center_word).
  { apply Hinfo; [apply center_is_in_whole_line_code|intros c H; contradiction|].
    apply singleton_zero_away_from_center. assumption. }
  specialize (Hz 62 ltac:(lia)). discriminate Hz.
Qed.

Theorem no_disjoint_whole_line_information_sets : forall p q,
  information (code_words whole_line_rows) [] p ->
  information (code_words whole_line_rows) [] q -> ~ disjoint_reserves p q.
Proof.
  intros p q Hp Hq Hdis.
  apply (Hdis 62 (whole_line_information_requires_center p Hp)).
  exact (whole_line_information_requires_center q Hq).
Qed.

Lemma empty_residual_is_whole_line_code : residual_rows initial_state = whole_line_rows.
Proof. vm_compute. reflexivity. Qed.

Theorem no_whole_line_linear_safe_empty : forall p q,
  ~ LinearSafe (code_words (residual_rows initial_state)) initial_state p q.
Proof.
  intros p q H. rewrite empty_residual_is_whole_line_code in H.
  destruct H as [_ _ Hdis Hp Hq _].
  exact (no_disjoint_whole_line_information_sets p q Hp Hq Hdis).
Qed.

Theorem every_whole_line_leaf_rejects_empty : forall decoder0 decoder1,
  linear_leafb decoder0 decoder1 initial_state = false.
Proof.
  intros d0 d1. destruct (linear_leafb d0 d1 initial_state) eqn:H; [|reflexivity].
  exfalso. apply (no_whole_line_linear_safe_empty (decoder_cells d0) (decoder_cells d1)).
  apply linear_leafb_sound. exact H.
Qed.

Print Assumptions nineteen_lines_isolate_center.
Print Assumptions no_disjoint_whole_line_information_sets.
Print Assumptions every_whole_line_leaf_rejects_empty.
