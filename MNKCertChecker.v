(** **************************************************************************
    MNKCertChecker.v: A SOUND Proof-Carrying Certificate Checker
    for Positional (m, n, k) Games

    - [cert]: a strategy tree for the attacking player [p]: either an
      immediately winning move, or a move followed by one sub-certificate per
      opponent reply.
    - [check_cert lines p d b ct]: decidable checker.  Compared to the previous
      version it additionally rejects (1) any branch in which the OPPONENT
      completes a line (in the strong game that is a loss for [p]), and
      (2) any non-winning move that fills the board (that is a draw).
    - [check_cert_sound]: a successful check PROVES the semantic statement
      [forces_win lines p d b] of MNKGame.v.  The bound [d] counts the
      attacker's own moves, so d = 4 means "within 7 plies" for Player 1.

    Zero axioms, zero admissions (closed under the global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.
Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.

(** Strategy certificates (mutual inductive so that the induction principle
    reaches the sub-certificates). *)
Inductive cert : Type :=
  | Imm : nat -> cert
  | Br : nat -> branches -> cert
with branches : Type :=
  | BNil : branches
  | BCons : nat -> cert -> branches -> branches.

Scheme cert_mut := Induction for cert Sort Prop
  with branches_mut := Induction for branches Sort Prop.

Fixpoint has_key (c : nat) (bs : branches) : bool :=
  match bs with
  | BNil => false
  | BCons c' _ rest => (c =? c') || has_key c rest
  end.

Fixpoint InB (c : nat) (sub : cert) (bs : branches) : Prop :=
  match bs with
  | BNil => False
  | BCons c' s rest => (c = c' /\ sub = s) \/ InB c sub rest
  end.

Lemma has_key_InB : forall c bs, has_key c bs = true -> exists sub, InB c sub bs.
Proof.
  intros c bs. induction bs as [| c' s rest IH]; simpl; [discriminate |].
  intros H. apply orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. subst. exists s. left. auto.
  - destruct (IH H) as [sub Hs]. exists sub. right. exact Hs.
Qed.

(** The move [cert_move ct replies] that the certificate prescribes after the
    given sequence of opponent replies (used to replay strategies). *)
Fixpoint find_sub (c : nat) (bs : branches) : option cert :=
  match bs with
  | BNil => None
  | BCons c' s rest => if c =? c' then Some s else find_sub c rest
  end.

Fixpoint cert_move (ct : cert) (replies : list nat) : option nat :=
  match ct, replies with
  | Imm m, [] => Some m
  | Br m _, [] => Some m
  | Br _ bs, c :: rs =>
      match find_sub c bs with
      | Some sub => cert_move sub rs
      | None => None
      end
  | Imm _, _ :: _ => None
  end.

Section Checker.

Variable lines : list (list nat).
Variable p : player.

Fixpoint check_cert (d : nat) (b : board_t) (ct : cert) {struct ct} : bool :=
  match ct with
  | Imm m =>
      match d with
      | 0 => false
      | S _ => is_legal_move b m && check_win (set_cell b m p) p lines
      end
  | Br m bs =>
      match d with
      | 0 => false
      | S d' =>
          let b1 := set_cell b m p in
          is_legal_move b m &&
          nonempty (legal_moves b1) &&
          forallb (fun c => has_key c bs) (legal_moves b1) &&
          check_branches d' b1 bs
      end
  end
with check_branches (d : nat) (b1 : board_t) (bs : branches) {struct bs} : bool :=
  match bs with
  | BNil => true
  | BCons c sub rest =>
      let b2 := set_cell b1 c (other_player p) in
      is_legal_move b1 c &&
      negb (check_win b2 (other_player p) lines) &&
      check_cert d b2 sub &&
      check_branches d b1 rest
  end.

Lemma check_branches_spec : forall bs d b1,
  check_branches d b1 bs = true ->
  forall c sub, InB c sub bs ->
    is_legal_move b1 c = true /\
    check_win (set_cell b1 c (other_player p)) (other_player p) lines = false /\
    check_cert d (set_cell b1 c (other_player p)) sub = true.
Proof.
  induction bs as [| c' s rest IH]; intros d b1 H c sub Hin; simpl in *; [contradiction |].
  apply andb_true_iff in H as [H Hrest].
  apply andb_true_iff in H as [H Hsub].
  apply andb_true_iff in H as [Hleg Hno].
  destruct Hin as [[-> ->] | Hin].
  - repeat split; auto. apply negb_true_iff. exact Hno.
  - eapply IH; eauto.
Qed.

(** Soundness: a certificate accepted by the checker is a genuine forced win. *)
Theorem check_cert_sound : forall ct d b,
  check_cert d b ct = true -> forces_win lines p d b.
Proof.
  apply (cert_mut
    (fun ct => forall d b, check_cert d b ct = true -> forces_win lines p d b)
    (fun bs => forall c sub, InB c sub bs ->
       forall d b, check_cert d b sub = true -> forces_win lines p d b)).
  - (* Imm *)
    intros m d b H. destruct d as [| d]; simpl in H; [discriminate |].
    apply andb_true_iff in H as [Hm Hw]. eapply fw_now; eauto.
  - (* Br *)
    intros m bs IHbs d b H. destruct d as [| d]; simpl in H; [discriminate |].
    apply andb_true_iff in H as [H Hbr].
    apply andb_true_iff in H as [H Hcov].
    apply andb_true_iff in H as [Hm Hne].
    rewrite forallb_forall in Hcov.
    assert (Hreply : forall c, is_legal_move (set_cell b m p) c = true ->
      check_win (set_cell (set_cell b m p) c (other_player p)) (other_player p) lines = false /\
      forces_win lines p d (set_cell (set_cell b m p) c (other_player p))).
    { intros c Hc. apply in_legal_moves in Hc.
      destruct (has_key_InB c bs (Hcov c Hc)) as [sub Hsub].
      destruct (check_branches_spec bs d _ Hbr c sub Hsub) as (_ & Hno & Hok).
      split; [exact Hno |]. eapply IHbs; eauto. }
    apply fw_next with (m := m); [exact Hm | | |].
    + apply nonempty_iff in Hne as [c Hc]. exists c. apply in_legal_moves. exact Hc.
    + intros c Hc. apply (Hreply c Hc).
    + intros c Hc. apply (Hreply c Hc).
  - (* BNil *)
    intros c sub [].
  - (* BCons *)
    intros c s Hs rest Hrest c' sub Hin d b Hck.
    destruct Hin as [[-> ->] | Hin].
    + eapply Hs; eauto.
    + eapply Hrest; eauto.
Qed.

End Checker.

Definition initial_board (num_cells : nat) : board_t :=
  empty_board num_cells.
