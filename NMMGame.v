(* ============================================================================== *)
(* NMMGame.v - Trusted Operational Semantics for Nine Men's Morris               *)
(* Three Phases: Placement, Movement, and Flying. Exact Mill Protection Rules.   *)
(* Verified for Rocq 9.1 with ZERO unproven axioms.                              *)
(* ============================================================================== *)

From Stdlib Require Import List Arith Bool Lia PeanoNat.
Import ListNotations.
Require Import NMM.NMMGraph.

Section NMMOperationalSemantics.

(** Player colors *)
Inductive color : Set :=
  | White : color
  | Black : color.

Definition opp (c : color) : color :=
  match c with
  | White => Black
  | Black => White
  end.

Lemma opp_involutive : forall c, opp (opp c) = c.
Proof. destruct c; reflexivity. Qed.

Lemma opp_neq : forall c, opp c <> c.
Proof. destruct c; discriminate. Qed.

Definition color_eqb (c1 c2 : color) : bool :=
  match c1, c2 with
  | White, White => true
  | Black, Black => true
  | _, _ => false
  end.

Lemma color_eqb_eq : forall c1 c2, color_eqb c1 c2 = true <-> c1 = c2.
Proof.
  destruct c1; destruct c2; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

(** Boolean list membership *)
Fixpoint in_nat_list (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => (x =? h) || in_nat_list x t
  end.

Lemma in_nat_list_iff : forall x l,
  in_nat_list x l = true <-> In x l.
Proof.
  intros x l. induction l as [| h t IH].
  - simpl. split; intros H; [discriminate | contradiction].
  - simpl. rewrite orb_true_iff, Nat.eqb_eq, IH.
    split; intros [-> | H]; [left; reflexivity | right; assumption | left; reflexivity | right; assumption].
Qed.

(** Board state: occupied positions for White and Black *)
Record board : Type := mkBoard {
  stones_white : list nat;
  stones_black : list nat
}.

Definition empty_board : board :=
  mkBoard [] [].

Definition player_stones (b : board) (c : color) : list nat :=
  match c with
  | White => stones_white b
  | Black => stones_black b
  end.

Definition is_occupied (b : board) (p : nat) : bool :=
  in_nat_list p (stones_white b) || in_nat_list p (stones_black b).

Definition count_stones (b : board) (c : color) : nat :=
  length (player_stones b c).

(** Mill detection for a player *)
Definition is_mill_complete (stones : list nat) (m : mill) : bool :=
  let '(a, b, c) := m in
  in_nat_list a stones && in_nat_list b stones && in_nat_list c stones.

Definition forms_mill_at (stones : list nat) (p : nat) : bool :=
  existsb (fun m =>
    point_in_mill p m && is_mill_complete stones m
  ) all_mills.

Definition stone_in_any_mill (stones : list nat) (p : nat) : bool :=
  existsb (fun m =>
    point_in_mill p m && is_mill_complete stones m
  ) all_mills.

Definition all_stones_in_mills (stones : list nat) : bool :=
  forallb (stone_in_any_mill stones) stones.

(** Legal capture rule:
    Cannot capture a stone in a completed mill, UNLESS all opponent stones are in mills.
*)
Definition is_legal_capture (b : board) (defender : color) (target : nat) : bool :=
  let opp_stones := player_stones b defender in
  in_nat_list target opp_stones &&
  (negb (stone_in_any_mill opp_stones target) || all_stones_in_mills opp_stones).

(** Board removal of a stone *)
Fixpoint remove_nat (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => if x =? h then t else h :: remove_nat x t
  end.

Definition remove_stone (b : board) (c : color) (target : nat) : board :=
  match c with
  | White => mkBoard (remove_nat target (stones_white b)) (stones_black b)
  | Black => mkBoard (stones_white b) (remove_nat target (stones_black b))
  end.

Definition add_stone (b : board) (c : color) (p : nat) : board :=
  match c with
  | White => mkBoard (p :: stones_white b) (stones_black b)
  | Black => mkBoard (stones_white b) (p :: stones_black b)
  end.

Definition move_stone (b : board) (c : color) (src dst : nat) : board :=
  add_stone (remove_stone b c src) c dst.

(** Game Phases *)
Inductive phase : Set :=
  | PhasePlacement (placed_w placed_b : nat)
  | PhaseMovement
  | PhaseFlying.

Record game_state : Type := mkState {
  current_turn : color;
  current_phase : phase;
  current_board : board
}.

Definition initial_state : game_state :=
  mkState White (PhasePlacement 0 0) empty_board.

(** Legal move types *)
Inductive move : Type :=
  | PlaceMove (dst : nat) (capture : option nat)
  | SlideMove (src dst : nat) (capture : option nat)
  | FlyMove   (src dst : nat) (capture : option nat).

(** Legal move predicates *)

(** 1. Placement Phase Move *)
Definition legal_placement (s : game_state) (dst : nat) (cap : option nat) : bool :=
  match current_phase s with
  | PhasePlacement pw pb =>
      let mover := current_turn s in
      let placed := match mover with White => pw | Black => pb end in
      (placed <? 9) &&
      is_point dst &&
      negb (is_occupied (current_board s) dst) &&
      let new_stones := dst :: player_stones (current_board s) mover in
      let formed := forms_mill_at new_stones dst in
      match cap with
      | Some target =>
          formed && is_legal_capture (current_board s) (opp mover) target
      | None =>
          negb formed
      end
  | _ => false
  end.

(** 2. Movement Phase Move (sliding along an edge when player has > 3 stones) *)
Definition legal_slide (s : game_state) (src dst : nat) (cap : option nat) : bool :=
  match current_phase s with
  | PhaseMovement | PhaseFlying =>
      let mover := current_turn s in
      (3 <? count_stones (current_board s) mover) &&
      in_nat_list src (player_stones (current_board s) mover) &&
      is_point dst &&
      negb (is_occupied (current_board s) dst) &&
      is_adjacent src dst &&
      let board_after_slide := move_stone (current_board s) mover src dst in
      let formed := forms_mill_at (player_stones board_after_slide mover) dst in
      match cap with
      | Some target =>
          formed && is_legal_capture board_after_slide (opp mover) target
      | None =>
          negb formed
      end
  | _ => false
  end.

(** 3. Flying Phase Move (jumping to any vacant point when player has = 3 stones) *)
Definition legal_fly (s : game_state) (src dst : nat) (cap : option nat) : bool :=
  match current_phase s with
  | PhaseMovement | PhaseFlying =>
      let mover := current_turn s in
      (count_stones (current_board s) mover =? 3) &&
      in_nat_list src (player_stones (current_board s) mover) &&
      is_point dst &&
      negb (is_occupied (current_board s) dst) &&
      let board_after_fly := move_stone (current_board s) mover src dst in
      let formed := forms_mill_at (player_stones board_after_fly mover) dst in
      match cap with
      | Some target =>
          formed && is_legal_capture board_after_fly (opp mover) target
      | None =>
          negb formed
      end
  | _ => false
  end.

Definition is_legal_move (s : game_state) (m : move) : bool :=
  match m with
  | PlaceMove dst cap => legal_placement s dst cap
  | SlideMove src dst cap => legal_slide s src dst cap
  | FlyMove src dst cap => legal_fly s src dst cap
  end.

(** Phase Transitions *)
Definition next_phase (p : phase) (mover : color) (b_next : board) : phase :=
  match p with
  | PhasePlacement pw pb =>
      let pw' := match mover with White => S pw | Black => pw end in
      let pb' := match mover with White => pb | Black => S pb end in
      if (pw' =? 9) && (pb' =? 9) then
        if (count_stones b_next White =? 3) || (count_stones b_next Black =? 3) then
          PhaseFlying
        else
          PhaseMovement
      else
        PhasePlacement pw' pb'
  | PhaseMovement =>
      if (count_stones b_next White =? 3) || (count_stones b_next Black =? 3) then
        PhaseFlying
      else
        PhaseMovement
  | PhaseFlying => PhaseFlying
  end.

Definition apply_move (s : game_state) (m : move) : game_state :=
  let mover := current_turn s in
  let b := current_board s in
  match m with
  | PlaceMove dst cap =>
      let b1 := add_stone b mover dst in
      let b2 := match cap with
                | Some target => remove_stone b1 (opp mover) target
                | None => b1
                end in
      mkState (opp mover) (next_phase (current_phase s) mover b2) b2
  | SlideMove src dst cap =>
      let b1 := move_stone b mover src dst in
      let b2 := match cap with
                | Some target => remove_stone b1 (opp mover) target
                | None => b1
                end in
      mkState (opp mover) (next_phase (current_phase s) mover b2) b2
  | FlyMove src dst cap =>
      let b1 := move_stone b mover src dst in
      let b2 := match cap with
                | Some target => remove_stone b1 (opp mover) target
                | None => b1
                end in
      mkState (opp mover) (next_phase (current_phase s) mover b2) b2
  end.

(** Inductive Transition Relation *)
Inductive step : game_state -> move -> game_state -> Prop :=
  | StepLegal : forall s m,
      is_legal_move s m = true ->
      step s m (apply_move s m).

(** Terminal status *)
Definition is_terminal_loss (s : game_state) (p : color) : bool :=
  match current_phase s with
  | PhasePlacement _ _ => false
  | _ =>
      (count_stones (current_board s) p <? 3)
  end.

(** Post-Placement Mobility Split Theorem:
    In both PhaseMovement and PhaseFlying, mobility is determined per-player
    by their stone count: a player with > 3 stones slides along adjacent edges
    (and cannot fly), while a player with = 3 stones flies to any vacant point
    (and cannot slide). This eliminates any phase deadlock when one player has
    3 stones and the opponent has > 3 stones.
*)
Theorem post_placement_mobility_split : forall c b src dst cap,
  (3 < count_stones b c ->
    legal_fly (mkState c PhaseMovement b) src dst cap = false /\
    legal_fly (mkState c PhaseFlying b) src dst cap = false /\
    legal_slide (mkState c PhaseFlying b) src dst cap =
    legal_slide (mkState c PhaseMovement b) src dst cap) /\
  (count_stones b c = 3 ->
    legal_slide (mkState c PhaseMovement b) src dst cap = false /\
    legal_slide (mkState c PhaseFlying b) src dst cap = false /\
    legal_fly (mkState c PhaseMovement b) src dst cap =
    legal_fly (mkState c PhaseFlying b) src dst cap).
Proof.
  intros c b src dst cap.
  split.
  - intros Hgt3.
    assert (Hneq : (count_stones b c =? 3) = false).
    { apply Nat.eqb_neq. lia. }
    unfold legal_fly, legal_slide. simpl.
    rewrite Hneq. simpl.
    repeat split; reflexivity.
  - intros Heq3.
    unfold legal_slide, legal_fly. simpl.
    rewrite Heq3. simpl.
    repeat split; reflexivity.
Qed.

End NMMOperationalSemantics.
