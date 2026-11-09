(** trusted/Rules.v: Canonical, Axiom-Free Game Model for 5x5x5 Qubic (5^3, k=5)
    QUBIC-PROOF-GATE-001 Specification Model.
    Completely self-contained; strictly 0 axioms, 0 admits. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. 125 CELLS AND 109 WINNING LINES                                         *)
(** ========================================================================= *)

Definition cell := nat.

Definition all_cells : list cell := seq 0 125.

Definition ortho_x_lines : list (list cell) :=
  [ [0; 1; 2; 3; 4]; [5; 6; 7; 8; 9];
    [10; 11; 12; 13; 14]; [15; 16; 17; 18; 19];
    [20; 21; 22; 23; 24]; [25; 26; 27; 28; 29];
    [30; 31; 32; 33; 34]; [35; 36; 37; 38; 39];
    [40; 41; 42; 43; 44]; [45; 46; 47; 48; 49];
    [50; 51; 52; 53; 54]; [55; 56; 57; 58; 59];
    [60; 61; 62; 63; 64]; [65; 66; 67; 68; 69];
    [70; 71; 72; 73; 74]; [75; 76; 77; 78; 79];
    [80; 81; 82; 83; 84]; [85; 86; 87; 88; 89];
    [90; 91; 92; 93; 94]; [95; 96; 97; 98; 99];
    [100; 101; 102; 103; 104]; [105; 106; 107; 108; 109];
    [110; 111; 112; 113; 114]; [115; 116; 117; 118; 119];
    [120; 121; 122; 123; 124] ].

Definition ortho_y_lines : list (list cell) :=
  [ [0; 5; 10; 15; 20]; [1; 6; 11; 16; 21];
    [2; 7; 12; 17; 22]; [3; 8; 13; 18; 23];
    [4; 9; 14; 19; 24]; [25; 30; 35; 40; 45];
    [26; 31; 36; 41; 46]; [27; 32; 37; 42; 47];
    [28; 33; 38; 43; 48]; [29; 34; 39; 44; 49];
    [50; 55; 60; 65; 70]; [51; 56; 61; 66; 71];
    [52; 57; 62; 67; 72]; [53; 58; 63; 68; 73];
    [54; 59; 64; 69; 74]; [75; 80; 85; 90; 95];
    [76; 81; 86; 91; 96]; [77; 82; 87; 92; 97];
    [78; 83; 88; 93; 98]; [79; 84; 89; 94; 99];
    [100; 105; 110; 115; 120]; [101; 106; 111; 116; 121];
    [102; 107; 112; 117; 122]; [103; 108; 113; 118; 123];
    [104; 109; 114; 119; 124] ].

Definition ortho_z_lines : list (list cell) :=
  [ [0; 25; 50; 75; 100]; [1; 26; 51; 76; 101];
    [2; 27; 52; 77; 102]; [3; 28; 53; 78; 103];
    [4; 29; 54; 79; 104]; [5; 30; 55; 80; 105];
    [6; 31; 56; 81; 106]; [7; 32; 57; 82; 107];
    [8; 33; 58; 83; 108]; [9; 34; 59; 84; 109];
    [10; 35; 60; 85; 110]; [11; 36; 61; 86; 111];
    [12; 37; 62; 87; 112]; [13; 38; 63; 88; 113];
    [14; 39; 64; 89; 114]; [15; 40; 65; 90; 115];
    [16; 41; 66; 91; 116]; [17; 42; 67; 92; 117];
    [18; 43; 68; 93; 118]; [19; 44; 69; 94; 119];
    [20; 45; 70; 95; 120]; [21; 46; 71; 96; 121];
    [22; 47; 72; 97; 122]; [23; 48; 73; 98; 123];
    [24; 49; 74; 99; 124] ].

Definition diag_xy_lines : list (list cell) :=
  [ [0; 6; 12; 18; 24]; [4; 8; 12; 16; 20];
    [25; 31; 37; 43; 49]; [29; 33; 37; 41; 45];
    [50; 56; 62; 68; 74]; [54; 58; 62; 66; 70];
    [75; 81; 87; 93; 99]; [79; 83; 87; 91; 95];
    [100; 106; 112; 118; 124]; [104; 108; 112; 116; 120] ].

Definition diag_xz_lines : list (list cell) :=
  [ [0; 26; 52; 78; 104]; [4; 28; 52; 76; 100];
    [5; 31; 57; 83; 109]; [9; 33; 57; 81; 105];
    [10; 36; 62; 88; 114]; [14; 38; 62; 86; 110];
    [15; 41; 67; 93; 119]; [19; 43; 67; 91; 115];
    [20; 46; 72; 98; 124]; [24; 48; 72; 96; 120] ].

Definition diag_yz_lines : list (list cell) :=
  [ [0; 30; 60; 90; 120]; [20; 40; 60; 80; 100];
    [1; 31; 61; 91; 121]; [21; 41; 61; 81; 101];
    [2; 32; 62; 92; 122]; [22; 42; 62; 82; 102];
    [3; 33; 63; 93; 123]; [23; 43; 63; 83; 103];
    [4; 34; 64; 94; 124]; [24; 44; 64; 84; 104] ].

Definition space_diag_lines : list (list cell) :=
  [ [0; 31; 62; 93; 124]; [4; 33; 62; 91; 120];
    [20; 41; 62; 83; 104]; [24; 43; 62; 81; 100] ].

Definition all_lines : list (list cell) :=
  ortho_x_lines ++ ortho_y_lines ++ ortho_z_lines ++
  diag_xy_lines ++ diag_xz_lines ++ diag_yz_lines ++
  space_diag_lines.

Theorem total_lines_count : length all_lines = 109%nat.
Proof. reflexivity. Qed.

Theorem total_cells_count : length all_cells = 125%nat.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 2. RESULTS AND WINNING CONDITION                                           *)
(** ========================================================================= *)

Inductive Result : Type :=
  | WhiteWins
  | BlackWins
  | Draw.

Definition has_line (stones : list cell) (l : list cell) : bool :=
  forallb (fun c => existsb (Nat.eqb c) stones) l.

Definition has_win (stones : list cell) : bool :=
  existsb (fun l => has_line stones l) all_lines.

(** ========================================================================= *)
(** 3. GAME STATE AND DETERMINISTIC TRANSITIONS                                *)
(** ========================================================================= *)

Record GameState : Type := make_state {
  white_stones : list cell;
  black_stones : list cell;
  history : list cell
}.

Definition initial_state : GameState := make_state [] [] [].

Definition occupied (st : GameState) (c : cell) : bool :=
  existsb (Nat.eqb c) (white_stones st) || existsb (Nat.eqb c) (black_stones st).

Definition is_legal_move (st : GameState) (c : cell) : bool :=
  (c <? 125)%nat && negb (occupied st c).

Definition next_available_cell (st : GameState) : cell :=
  let fix find_first (n : nat) : cell :=
    match n with
    | O => 0%nat
    | S m =>
      let c := (125 - n)%nat in
      if negb (occupied st c) then c
      else find_first m
    end
  in find_first 125%nat.

(** Strategies are total policies on all reachable game states *)
Definition WhiteStrategy : Type := GameState -> cell.
Definition BlackStrategy : Type := GameState -> cell.

Record GameTrace : Type := make_trace {
  final_state : GameState;
  final_result : Result
}.

Fixpoint step_game (steps_remaining : nat) (turn_white : bool) (st : GameState)
                   (w_strat : WhiteStrategy) (b_strat : BlackStrategy) : GameTrace :=
  match steps_remaining with
  | O => make_trace st Draw
  | S rem =>
    if turn_white then
      let c_req := w_strat st in
      let c := if is_legal_move st c_req then c_req else next_available_cell st in
      let new_white := c :: white_stones st in
      let new_st := make_state new_white (black_stones st) (c :: history st) in
      if has_win new_white then make_trace new_st WhiteWins
      else if (length (history new_st) =? 125)%nat then make_trace new_st Draw
      else step_game rem false new_st w_strat b_strat
    else
      let c_req := b_strat st in
      let c := if is_legal_move st c_req then c_req else next_available_cell st in
      let new_black := c :: black_stones st in
      let new_st := make_state (white_stones st) new_black (c :: history st) in
      if has_win new_black then make_trace new_st BlackWins
      else if (length (history new_st) =? 125)%nat then make_trace new_st Draw
      else step_game rem true new_st w_strat b_strat
  end.

Definition play (w : WhiteStrategy) (b : BlackStrategy) : GameTrace :=
  step_game 125%nat true initial_state w b.

Definition outcome (tr : GameTrace) : Result :=
  final_result tr.

(** Non-vacuity witnesses: both strategy types are inhabited *)
Definition default_white : WhiteStrategy := fun _ => 0%nat.
Definition default_black : BlackStrategy := fun _ => 0%nat.
