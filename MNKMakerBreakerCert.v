(** * MNKMakerBreakerCert.v: A Sound Checker for Maker-Breaker Wins

    - [mbcert]: a strategy tree for Maker.  Each node is a Maker move,
      followed by one sub-certificate for every Breaker reply that does not
      leave Maker a winning cell.
    - [check_mb lines p d b ct]: decidable checker.  Breaker's own lines are
      irrelevant (Maker-Breaker rules).  A Breaker reply that leaves Maker a
      cell completing a line needs no sub-certificate: the checker finds that
      cell itself ([quick_win]).  So when Maker makes a threat, only the
      blocking reply is listed.
    - [check_mb_sound]: an accepted certificate proves [maker_wins].  The
      bound [d] counts Maker's own moves.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame MNKErdosSelfridge.

Inductive mbcert : Type :=
  | MB : nat -> mbreplies -> mbcert
with mbreplies : Type :=
  | RNil : mbreplies
  | RCons : nat -> mbcert -> mbreplies -> mbreplies.

Scheme mbcert_mut := Induction for mbcert Sort Prop
  with mbreplies_mut := Induction for mbreplies Sort Prop.

Fixpoint has_reply (c : nat) (rs : mbreplies) : bool :=
  match rs with
  | RNil => false
  | RCons c' _ rest => (c =? c') || has_reply c rest
  end.

Fixpoint InR (c : nat) (sub : mbcert) (rs : mbreplies) : Prop :=
  match rs with
  | RNil => False
  | RCons c' s rest => (c = c' /\ sub = s) \/ InR c sub rest
  end.

Lemma has_reply_InR : forall c rs, has_reply c rs = true -> exists sub, InR c sub rs.
Proof.
  intros c rs. induction rs as [| c' s rest IH]; simpl; [discriminate |].
  intros H. apply orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. subst. exists s. left. auto.
  - destruct (IH H) as [sub Hs]. exists sub. right. exact Hs.
Qed.

(** Number of Maker moves in a certificate (its nodes). *)
Fixpoint mbcert_size (ct : mbcert) : nat :=
  match ct with
  | MB _ rs => S (mbreplies_size rs)
  end
with mbreplies_size (rs : mbreplies) : nat :=
  match rs with
  | RNil => 0
  | RCons _ sub rest => mbcert_size sub + mbreplies_size rest
  end.

Section Checker.

Variable lines : list (list nat).
Variable p : player.

(** Line [L] lacks exactly one Maker stone, on an empty cell: Maker completes
    it at once.  (A Breaker stone on [L] would be a second non-Maker cell.) *)
Definition threat_line (b : board_t) (L : list nat) : bool :=
  match filter (fun x => negb (cell_owned_by b p x)) L with
  | [x] => is_legal_move b x
  | _ => false
  end.

Lemma threat_line_win : forall b L, In L lines -> threat_line b L = true ->
  exists x, is_legal_move b x = true /\ check_win (set_cell b x p) p lines = true.
Proof.
  intros b L HL H. unfold threat_line in H.
  destruct (filter (fun x => negb (cell_owned_by b p x)) L) as [| x [| y rest]] eqn:Ef;
    try discriminate.
  exists x. split; [exact H |].
  apply check_win_iff. exists L. split; [exact HL |].
  intros y Hy. destruct (Nat.eq_dec y x) as [-> | Hyx].
  - apply get_set_cell_same. apply legal_move_lt. exact H.
  - rewrite get_set_cell_other by congruence.
    apply cell_owned_iff.
    destruct (cell_owned_by b p y) eqn:Eo; [reflexivity |].
    exfalso. assert (Hin : In y (filter (fun x => negb (cell_owned_by b p x)) L)).
    { apply filter_In. rewrite Eo. split; [exact Hy | reflexivity]. }
    rewrite Ef in Hin. destruct Hin as [Hin | []]. congruence.
Qed.

(** Maker, to move with at least one move left, has a cell completing a line. *)
Definition quick_win (d : nat) (b : board_t) : bool :=
  match d with
  | 0 => false
  | S _ => existsb (threat_line b) lines
  end.

Lemma quick_win_sound : forall d b, quick_win d b = true -> maker_wins lines p d b.
Proof.
  intros [| d] b H; simpl in H; [discriminate |].
  apply existsb_exists in H as [L [HL Ht]].
  destruct (threat_line_win b L HL Ht) as [x [Hx Hw]].
  exact (mw_now lines p d b x Hx Hw).
Qed.

Fixpoint check_mb (d : nat) (b : board_t) (ct : mbcert) {struct ct} : bool :=
  match ct with
  | MB m rs =>
      match d with
      | 0 => false
      | S d' =>
          let b1 := set_cell b m p in
          is_legal_move b m &&
          (check_win b1 p lines ||
           (nonempty (legal_moves b1) &&
            forallb (fun c => has_reply c rs ||
                              quick_win d' (set_cell b1 c (other_player p)))
                    (legal_moves b1) &&
            check_replies d' b1 rs))
      end
  end
with check_replies (d : nat) (b1 : board_t) (rs : mbreplies) {struct rs} : bool :=
  match rs with
  | RNil => true
  | RCons c sub rest =>
      check_mb d (set_cell b1 c (other_player p)) sub && check_replies d b1 rest
  end.

Lemma check_replies_spec : forall rs d b1,
  check_replies d b1 rs = true ->
  forall c sub, InR c sub rs -> check_mb d (set_cell b1 c (other_player p)) sub = true.
Proof.
  induction rs as [| c' s rest IH]; intros d b1 H c sub Hin; simpl in *; [contradiction |].
  apply andb_true_iff in H as [Hs Hrest].
  destruct Hin as [[-> ->] | Hin].
  - exact Hs.
  - eapply IH; eauto.
Qed.

(** Soundness: a certificate accepted by the checker is a genuine Maker win. *)
Theorem check_mb_sound : forall ct d b,
  check_mb d b ct = true -> maker_wins lines p d b.
Proof.
  apply (mbcert_mut
    (fun ct => forall d b, check_mb d b ct = true -> maker_wins lines p d b)
    (fun rs => forall c sub, InR c sub rs ->
       forall d b, check_mb d b sub = true -> maker_wins lines p d b)).
  - (* a Maker node *)
    intros m rs IHrs d b H. destruct d as [| d]; simpl in H; [discriminate |].
    apply andb_true_iff in H as [Hm H].
    apply orb_true_iff in H as [Hw | H].
    + exact (mw_now lines p d b m Hm Hw).
    + apply andb_true_iff in H as [H Hrs].
      apply andb_true_iff in H as [Hne Hcov].
      rewrite forallb_forall in Hcov.
      apply (mw_next lines p d b m Hm).
      * apply nonempty_iff in Hne as [c Hc]. exists c. apply in_legal_moves. exact Hc.
      * intros c Hc. apply in_legal_moves in Hc.
        pose proof (Hcov c Hc) as Hcc. apply orb_true_iff in Hcc as [Hk | Hq].
        -- destruct (has_reply_InR c rs Hk) as [sub Hsub].
           apply (IHrs c sub Hsub).
           exact (check_replies_spec rs d _ Hrs c sub Hsub).
        -- exact (quick_win_sound d _ Hq).
  - (* RNil *)
    intros c sub [].
  - (* RCons *)
    intros c s Hs rest Hrest c' sub Hin d b Hck.
    destruct Hin as [[-> ->] | Hin].
    + exact (Hs d b Hck).
    + exact (Hrest c' sub Hin d b Hck).
Qed.

End Checker.
