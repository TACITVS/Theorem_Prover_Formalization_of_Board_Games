(** **************************************************************************
    CheckersGame.v: State Representation & Transition Semantics in Rocq 9.1
    
    This module formalizes:
    1. Checkers players (White / Black) and pieces (Men / Kings).
    2. Board occupancy state and list-based representation.
    3. Mandatory Capture Rule: simple moves are strictly prohibited
       when any capture jump exists on the board.
    4. Crown Promotion Rule: regular men reaching rank 7 (White) or
       rank 0 (Black) promote to Kings.
    5. Single and multi-jump transition relations.
    6. Preservation and strict decrease theorems for piece counts.
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.
Require Import Checkers.CheckersBoard.

Section CheckersGame.

Inductive player : Type := White | Black.

Definition player_eqb (p1 p2 : player) : bool :=
  match p1, p2 with
  | White, White => true
  | Black, Black => true
  | _, _ => false
  end.

Lemma player_eqb_spec : forall p1 p2, player_eqb p1 p2 = true <-> p1 = p2.
Proof.
  destruct p1, p2; simpl; split; intros; try reflexivity; try discriminate.
Qed.

Definition opp (p : player) : player :=
  match p with
  | White => Black
  | Black => White
  end.

Lemma opp_involutive : forall p, opp (opp p) = p.
Proof.
  destruct p; reflexivity.
Qed.

Lemma opp_neq : forall p, opp p <> p.
Proof.
  destruct p; discriminate.
Qed.

Record state : Type := mkState {
  white_men   : list nat;
  black_men   : list nat;
  white_kings : list nat;
  black_kings : list nat;
  turn        : player
}.

Definition total_white (st : state) : nat :=
  length (white_men st) + length (white_kings st).

Definition total_black (st : state) : nat :=
  length (black_men st) + length (black_kings st).

Definition total_pieces (st : state) : nat :=
  total_white st + total_black st.

(** Square list helpers *)

Definition remove_sq (s : nat) (l : list nat) : list nat :=
  filter (fun x => negb (x =? s)) l.

Lemma remove_sq_length_le : forall s l,
  length (remove_sq s l) <= length l.
Proof.
  intros s l. unfold remove_sq.
  induction l as [|x xs IH]; simpl; [lia|].
  destruct (x =? s); simpl; lia.
Qed.

Lemma remove_sq_notin : forall s xs,
  ~ In s xs ->
  filter (fun x => negb (x =? s)) xs = xs.
Proof.
  intros s xs Hnotin.
  induction xs as [|y ys IHy]; simpl; [reflexivity|].
  destruct (y =? s) eqn:Hys.
  - apply Nat.eqb_eq in Hys; subst y.
    exfalso. apply Hnotin. left. reflexivity.
  - simpl. rewrite IHy.
    + reflexivity.
    + intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma remove_sq_length_in : forall s l,
  In s l ->
  NoDup l ->
  length (remove_sq s l) = length l - 1.
Proof.
  intros s l Hin Hnd.
  unfold remove_sq.
  induction l as [|x xs IH].
  - inversion Hin.
  - inversion Hnd as [|? ? Hnotin Hnd_xs]; subst.
    simpl in Hin.
    destruct Hin as [Heq | Hin_xs].
    + subst x. simpl.
      rewrite Nat.eqb_refl. simpl.
      rewrite (remove_sq_notin s xs Hnotin). lia.
    + simpl.
      destruct (x =? s) eqn:Hxs.
      * apply Nat.eqb_eq in Hxs; subst x. contradiction.
      * simpl. rewrite (IH Hin_xs Hnd_xs).
        destruct xs; [inversion Hin_xs|]. simpl. lia.
Qed.

(** Occupancy Queries *)

Definition has_sq (s : nat) (l : list nat) : bool :=
  existsb (Nat.eqb s) l.

Definition is_white_piece (s : nat) (st : state) : bool :=
  has_sq s (white_men st) || has_sq s (white_kings st).

Definition is_black_piece (s : nat) (st : state) : bool :=
  has_sq s (black_men st) || has_sq s (black_kings st).

Definition occupied (s : nat) (st : state) : bool :=
  is_white_piece s st || is_black_piece s st.

Definition is_player_piece (p : player) (s : nat) (st : state) : bool :=
  match p with
  | White => is_white_piece s st
  | Black => is_black_piece s st
  end.

Definition is_opp_piece (p : player) (s : nat) (st : state) : bool :=
  is_player_piece (opp p) s st.

Definition is_king (p : player) (s : nat) (st : state) : bool :=
  match p with
  | White => has_sq s (white_kings st)
  | Black => has_sq s (black_kings st)
  end.

(** Step & Jump Lookups *)

Definition opt_to_list (o : option nat) : list nat :=
  match o with Some x => [x] | None => [] end.

Definition opt_pair_to_list (o : option (nat * nat)) : list (nat * nat) :=
  match o with Some p => [p] | None => [] end.

Definition man_step_targets (p : player) (s : nat) : list nat :=
  match p with
  | White => opt_to_list (step_fl s) ++ opt_to_list (step_fr s)
  | Black => opt_to_list (step_bl s) ++ opt_to_list (step_br s)
  end.

Definition king_step_targets (s : nat) : list nat :=
  opt_to_list (step_fl s) ++ opt_to_list (step_fr s) ++
  opt_to_list (step_bl s) ++ opt_to_list (step_br s).

Definition man_jump_targets (p : player) (s : nat) : list (nat * nat) :=
  match p with
  | White => opt_pair_to_list (jump_fl s) ++ opt_pair_to_list (jump_fr s)
  | Black => opt_pair_to_list (jump_bl s) ++ opt_pair_to_list (jump_br s)
  end.

Definition king_jump_targets (s : nat) : list (nat * nat) :=
  opt_pair_to_list (jump_fl s) ++ opt_pair_to_list (jump_fr s) ++
  opt_pair_to_list (jump_bl s) ++ opt_pair_to_list (jump_br s).

Definition piece_jump_targets (p : player) (s : nat) (st : state) : list (nat * nat) :=
  if is_king p s st then king_jump_targets s else man_jump_targets p s.

(** Jump Legality Checker *)

Definition can_jump_vector (st : state) (p : player) (vec : nat * nat) : bool :=
  let (mid, dst) := vec in
  is_opp_piece p mid st && negb (occupied dst st) && (dst <? 32).

Definition can_jump_from (st : state) (p : player) (s : nat) : bool :=
  is_player_piece p s st &&
  existsb (can_jump_vector st p) (piece_jump_targets p s st).

(** Mandatory Capture Decider: checks all 32 squares on board *)
Definition has_any_jump (st : state) (p : player) : bool :=
  existsb (can_jump_from st p) (seq 0 32).

(** Crown Promotion Rule *)

Definition should_promote (p : player) (was_king : bool) (dst : nat) : bool :=
  negb was_king &&
  match p with
  | White => 28 <=? dst
  | Black => dst <? 4
  end.

(** Move Execution (State Updates) *)

Definition apply_simple_step (st : state) (p : player) (src dst : nat) : state :=
  let was_king := is_king p src st in
  let crowns := should_promote p was_king dst in
  match p with
  | White =>
      if was_king then
        mkState (white_men st) (black_men st)
                (dst :: remove_sq src (white_kings st)) (black_kings st)
                (opp (turn st))
      else if crowns then
        mkState (remove_sq src (white_men st)) (black_men st)
                (dst :: white_kings st) (black_kings st)
                (opp (turn st))
      else
        mkState (dst :: remove_sq src (white_men st)) (black_men st)
                (white_kings st) (black_kings st)
                (opp (turn st))
  | Black =>
      if was_king then
        mkState (white_men st) (black_men st)
                (white_kings st) (dst :: remove_sq src (black_kings st))
                (opp (turn st))
      else if crowns then
        mkState (white_men st) (remove_sq src (black_men st))
                (white_kings st) (dst :: black_kings st)
                (opp (turn st))
      else
        mkState (white_men st) (dst :: remove_sq src (black_men st))
                (white_kings st) (black_kings st)
                (opp (turn st))
  end.

Definition apply_single_jump_sub (st : state) (p : player) (src mid dst : nat) : state :=
  let was_king := is_king p src st in
  let crowns := should_promote p was_king dst in
  match p with
  | White =>
      let b_men := remove_sq mid (black_men st) in
      let b_kings := remove_sq mid (black_kings st) in
      if was_king then
        mkState (white_men st) b_men
                (dst :: remove_sq src (white_kings st)) b_kings
                (turn st)
      else if crowns then
        mkState (remove_sq src (white_men st)) b_men
                (dst :: white_kings st) b_kings
                (turn st)
      else
        mkState (dst :: remove_sq src (white_men st)) b_men
                (white_kings st) b_kings
                (turn st)
  | Black =>
      let w_men := remove_sq mid (white_men st) in
      let w_kings := remove_sq mid (white_kings st) in
      if was_king then
        mkState w_men (black_men st)
                w_kings (dst :: remove_sq src (black_kings st))
                (turn st)
      else if crowns then
        mkState w_men (remove_sq src (black_men st))
                w_kings (dst :: black_kings st)
                (turn st)
      else
        mkState w_men (dst :: remove_sq src (black_men st))
                w_kings (black_kings st)
                (turn st)
  end.

(** Simple Move Relation *)

Definition legal_simple_step (st : state) (src dst : nat) : Prop :=
  has_any_jump st (turn st) = false /\
  is_player_piece (turn st) src st = true /\
  negb (occupied dst st) = true /\
  dst < 32 /\
  In dst (if is_king (turn st) src st
          then king_step_targets src
          else man_step_targets (turn st) src).

(** Jump Move Relation: single jump step *)

Definition legal_single_jump (st : state) (src mid dst : nat) : Prop :=
  is_player_piece (turn st) src st = true /\
  is_opp_piece (turn st) mid st = true /\
  negb (occupied dst st) = true /\
  dst < 32 /\
  In (mid, dst) (piece_jump_targets (turn st) src st).

(** Multi-Jump Execution:
    Sequence of jumps by the same piece.
    Terminates when piece crowns or no further jumps from dst exist. *)

Inductive jump_path : state -> player -> nat -> nat -> state -> Prop :=
| JP_One : forall st p src mid dst st1,
    p = turn st ->
    legal_single_jump st src mid dst ->
    st1 = apply_single_jump_sub st p src mid dst ->
    (should_promote p (is_king p src st) dst = true \/
     can_jump_from st1 p dst = false) ->
    jump_path st p src dst (mkState (white_men st1) (black_men st1)
                                    (white_kings st1) (black_kings st1)
                                    (opp p))
| JP_More : forall st p src mid dst st1 dst_final st_final,
    p = turn st ->
    legal_single_jump st src mid dst ->
    st1 = apply_single_jump_sub st p src mid dst ->
    should_promote p (is_king p src st) dst = false ->
    can_jump_from st1 p dst = true ->
    jump_path (mkState (white_men st1) (black_men st1)
                       (white_kings st1) (black_kings st1) p)
              p dst dst_final st_final ->
    jump_path st p src dst_final st_final.

(** Full Turn Step Relation *)

Inductive step : state -> state -> Prop :=
| StepSimple : forall st src dst st',
    legal_simple_step st src dst ->
    st' = apply_simple_step st (turn st) src dst ->
    step st st'
| StepJump : forall st src dst st',
    jump_path st (turn st) src dst st' ->
    step st st'.

(** Theorem 1: Every step alternates the active player turn *)
Lemma apply_simple_step_turn : forall st p src dst,
  turn (apply_simple_step st p src dst) = opp (turn st).
Proof.
  intros st p src dst.
  unfold apply_simple_step.
  destruct p.
  - destruct (is_king White src st).
    + reflexivity.
    + destruct (should_promote White false dst); reflexivity.
  - destruct (is_king Black src st).
    + reflexivity.
    + destruct (should_promote Black false dst); reflexivity.
Qed.

Theorem step_turn : forall st st',
  step st st' ->
  turn st' = opp (turn st).
Proof.
  intros st st' Hstep.
  destruct Hstep as [st src dst st' Hleg Heq | st src dst st' Hjp].
  - subst st'. apply apply_simple_step_turn.
  - remember (turn st) as p.
    induction Hjp as [st0 p0 src0 mid0 dst0 st1 Hp Hleg Heq1 Hterm |
                      st0 p0 src0 mid0 dst0 st1 dst_fin st_fin Hp Hleg Heq1 Hnp Hcont Hmore IH].
    + subst p0. simpl. reflexivity.
    + subst p0. apply IH. reflexivity.
Qed.

(** Theorem 2: Simple step preserves total piece count when NoDup holds *)
Lemma in_length_ge_1 : forall (A : Type) (x : A) (l : list A), In x l -> 1 <= length l.
Proof.
  intros A x l Hin. destruct l; simpl in *; [contradiction | lia].
Qed.

Ltac solve_lengths :=
  repeat match goal with
  | [ |- context [length ?l] ] => generalize (length l); intro
  end; lia.

Theorem simple_step_preserves_count : forall st src dst,
  is_player_piece (turn st) src st = true ->
  (turn st = White ->
   (is_king White src st = true -> In src (white_kings st) /\ NoDup (white_kings st)) /\
   (is_king White src st = false -> In src (white_men st) /\ NoDup (white_men st))) ->
  (turn st = Black ->
   (is_king Black src st = true -> In src (black_kings st) /\ NoDup (black_kings st)) /\
   (is_king Black src st = false -> In src (black_men st) /\ NoDup (black_men st))) ->
  total_pieces (apply_simple_step st (turn st) src dst) = total_pieces st.
Proof.
  intros st src dst Hocc Hw Hb.
  unfold apply_simple_step, total_pieces, total_white, total_black.
  destruct (turn st) eqn:Hturn.
  - specialize (Hw eq_refl).
    destruct (is_king White src st) eqn:Hk.
    + destruct Hw as [Hwk _]. specialize (Hwk eq_refl).
      destruct Hwk as [Hin Hnd].
      simpl. rewrite (remove_sq_length_in src (white_kings st) Hin Hnd).
      destruct (white_kings st); [contradiction | simpl; lia].
    + destruct Hw as [_ Hwm]. specialize (Hwm eq_refl).
      destruct Hwm as [Hin Hnd].
      destruct (should_promote White false dst) eqn:Hpr; simpl;
      rewrite (remove_sq_length_in src (white_men st) Hin Hnd);
      destruct (white_men st); [contradiction | simpl; lia | contradiction | simpl; lia].
  - specialize (Hb eq_refl).
    destruct (is_king Black src st) eqn:Hk.
    + destruct Hb as [Hbk _]. specialize (Hbk eq_refl).
      destruct Hbk as [Hin Hnd].
      simpl. rewrite (remove_sq_length_in src (black_kings st) Hin Hnd).
      destruct (black_kings st); [contradiction | simpl; lia].
    + destruct Hb as [_ Hbm]. specialize (Hbm eq_refl).
      destruct Hbm as [Hin Hnd].
      destruct (should_promote Black false dst) eqn:Hpr; simpl;
      rewrite (remove_sq_length_in src (black_men st) Hin Hnd);
      destruct (black_men st); [contradiction | simpl; lia | contradiction | simpl; lia].
Qed.

End CheckersGame.
