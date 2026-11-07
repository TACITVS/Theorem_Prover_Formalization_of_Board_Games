(** * Connect-5 with gravity on an 8-column x 8-row board

    This file is the TRUSTED SPECIFICATION: the rules of the game and the
    meaning of "a player can avoid losing".  Everything else in the
    development is proved from these definitions.

    - Columns are numbered 0..7 (left to right), rows 0..7 (bottom to top).
    - A board is a list of 8 columns; each column lists its discs from the
      bottom up.  A move drops a disc on top of a non-full column.
    - White moves first.  The first player to own all 5 cells of a winning
      line (horizontal, vertical or diagonal) wins.  If the board fills up
      with nobody having won, the game is a draw. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

Inductive player : Type := White | Black.

Definition other (p : player) : player :=
  match p with White => Black | Black => White end.

Definition peqb (p q : player) : bool :=
  match p, q with
  | White, White | Black, Black => true
  | _, _ => false
  end.

Definition board : Type := list (list player).
Definition cell : Type := (nat * nat)%type.          (* (column, row) *)

Definition col (b : board) (c : nat) : list player := nth c b [].

(** The disc (if any) at a cell. *)
Definition owner (b : board) (x : cell) : option player :=
  nth_error (col b (fst x)) (snd x).

(** A move in column [c] is legal iff [c] is a column and it is not full. *)
Definition legal (b : board) (c : nat) : bool :=
  (c <? 8) && (length (col b c) <? 8).

Fixpoint replace {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S n' => h :: replace t n' v
  end.

(** Gravity: the disc lands on top of column [c]. *)
Definition play (b : board) (c : nat) (p : player) : board :=
  replace b c (col b c ++ [p]).

Definition full (b : board) : bool :=
  forallb (fun c => negb (legal b c)) (seq 0 8).

Definition initial : board := repeat [] 8.

(** ** The 96 winning lines *)
Definition hline (c r : nat) : list cell := map (fun i => (c + i, r)) (seq 0 5).
Definition vline (c r : nat) : list cell := map (fun i => (c, r + i)) (seq 0 5).
Definition dline (c r : nat) : list cell := map (fun i => (c + i, r + i)) (seq 0 5).
Definition aline (c r : nat) : list cell := map (fun i => (c + i, r + 4 - i)) (seq 0 5).

Definition lines : list (list cell) :=
     flat_map (fun c => map (hline c) (seq 0 8)) (seq 0 4)    (* 32 horizontal  *)
  ++ flat_map (fun c => map (vline c) (seq 0 4)) (seq 0 8)    (* 32 vertical    *)
  ++ flat_map (fun c => map (dline c) (seq 0 4)) (seq 0 4)    (* 16 diagonal /  *)
  ++ flat_map (fun c => map (aline c) (seq 0 4)) (seq 0 4).   (* 16 diagonal \  *)

Definition owned_by (b : board) (p : player) (x : cell) : bool :=
  match owner b x with Some q => peqb q p | None => false end.

(** [p] owns every cell of some winning line. *)
Definition has_line (b : board) (p : player) : bool :=
  existsb (fun L => forallb (owned_by b p) L) lines.

(** ** Game semantics

    [safe d b s]: in position [b], with [s] to move and nobody having won
    yet, player [d] (the defender) has a strategy guaranteeing that the
    opponent never completes a line: the game ends with a full board or
    with [d] completing a line first.  In other words, [d] can force at
    least a draw. *)
Inductive safe (d : player) : board -> player -> Prop :=
| safe_full : forall b s,
    full b = true -> safe d b s
| safe_def : forall b c,
    legal b c = true ->
    (has_line (play b c d) d = true \/ safe d (play b c d) (other d)) ->
    safe d b d
| safe_att : forall b,
    full b = false ->
    (forall c, legal b c = true ->
       has_line (play b c (other d)) (other d) = false /\
       safe d (play b c (other d)) d) ->
    safe d b (other d).

(** ** Minimax value, from the point of view of the player to move *)
Inductive result : Type := Loss | Draw | Win.

Definition neg (r : result) : result :=
  match r with Loss => Win | Draw => Draw | Win => Loss end.

Definition rank (r : result) : nat :=
  match r with Loss => 0 | Draw => 1 | Win => 2 end.

Definition rmax (r1 r2 : result) : result :=
  if rank r1 <? rank r2 then r2 else r1.

Fixpoint value (fuel : nat) (b : board) (s : player) : result :=
  match fuel with
  | O => Draw
  | S f =>
      if full b then Draw
      else fold_left
             (fun acc c =>
                if legal b c then
                  rmax acc (if has_line (play b c s) s then Win
                            else neg (value f (play b c s) (other s)))
                else acc)
             (seq 0 8) Loss
  end.

(** The value of the game: 64 is the number of cells, so the recursion
    never runs out of fuel before the board is full. *)
Definition game_value : result := value 64 initial White.
