(** QubicBoard.v: 5x5x5 3D Tic-Tac-Toe Geometry, 109 Winning Lines, and O_h Orbits in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. COORDINATES AND 125-CELL GRID                                           *)
(** ========================================================================= *)

Definition cell := nat.

Definition cell_x (c : cell) : nat := c mod 5.
Definition cell_y (c : cell) : nat := (c / 5) mod 5.
Definition cell_z (c : cell) : nat := c / 25.

Definition make_cell (x y z : nat) : cell := 25 * z + 5 * y + x.

Definition all_cells : list cell := seq 0 125.

Theorem all_cells_length : length all_cells = 125.
Proof. reflexivity. Qed.

Theorem all_cells_NoDup : NoDup all_cells.
Proof. apply seq_NoDup. Qed.

Lemma make_cell_decomp : forall x y z : nat,
  x < 5 -> y < 5 -> z < 5 ->
  cell_x (make_cell x y z) = x /\
  cell_y (make_cell x y z) = y /\
  cell_z (make_cell x y z) = z.
Proof.
  intros x y z Hx Hy Hz.
  unfold cell_x, cell_y, cell_z, make_cell.
  repeat (destruct x as [|x]; [|try lia]);
  repeat (destruct y as [|y]; [|try lia]);
  repeat (destruct z as [|z]; [|try lia]);
  repeat split; reflexivity.
Qed.

Lemma make_cell_bound : forall x y z : nat,
  x < 5 -> y < 5 -> z < 5 ->
  make_cell x y z < 125.
Proof.
  intros x y z Hx Hy Hz.
  unfold make_cell. lia.
Qed.

(** ========================================================================= *)
(** 2. ENUMERATION OF ALL 109 WINNING LINES                                     *)
(** ========================================================================= *)

(** 25 Orthogonal X-lines (varying x in 0..4) *)
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

(** 25 Orthogonal Y-lines (varying y in 0..4) *)
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

(** 25 Orthogonal Z-lines (varying z in 0..4) *)
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

(** 10 Planar Diagonals in XY-planes (z in 0..4) *)
Definition diag_xy_lines : list (list cell) :=
  [ [0; 6; 12; 18; 24]; [4; 8; 12; 16; 20];
    [25; 31; 37; 43; 49]; [29; 33; 37; 41; 45];
    [50; 56; 62; 68; 74]; [54; 58; 62; 66; 70];
    [75; 81; 87; 93; 99]; [79; 83; 87; 91; 95];
    [100; 106; 112; 118; 124]; [104; 108; 112; 116; 120] ].

(** 10 Planar Diagonals in XZ-planes (y in 0..4) *)
Definition diag_xz_lines : list (list cell) :=
  [ [0; 26; 52; 78; 104]; [4; 28; 52; 76; 100];
    [5; 31; 57; 83; 109]; [9; 33; 57; 81; 105];
    [10; 36; 62; 88; 114]; [14; 38; 62; 86; 110];
    [15; 41; 67; 93; 119]; [19; 43; 67; 91; 115];
    [20; 46; 72; 98; 124]; [24; 48; 72; 96; 120] ].

(** 10 Planar Diagonals in YZ-planes (x in 0..4) *)
Definition diag_yz_lines : list (list cell) :=
  [ [0; 30; 60; 90; 120]; [20; 40; 60; 80; 100];
    [1; 31; 61; 91; 121]; [21; 41; 61; 81; 101];
    [2; 32; 62; 92; 122]; [22; 42; 62; 82; 102];
    [3; 33; 63; 93; 123]; [23; 43; 63; 83; 103];
    [4; 34; 64; 94; 124]; [24; 44; 64; 84; 104] ].

(** 4 3D Space Diagonals (Triagonals through opposite corners) *)
Definition space_diag_lines : list (list cell) :=
  [ [0; 31; 62; 93; 124]; [4; 33; 62; 91; 120];
    [20; 41; 62; 83; 104]; [24; 43; 62; 81; 100] ].

(** The Master Set of All 109 Winning Lines *)
Definition all_lines : list (list cell) :=
  ortho_x_lines ++ ortho_y_lines ++ ortho_z_lines ++
  diag_xy_lines ++ diag_xz_lines ++ diag_yz_lines ++
  space_diag_lines.

Theorem ortho_x_lines_count : length ortho_x_lines = 25.
Proof. reflexivity. Qed.

Theorem ortho_y_lines_count : length ortho_y_lines = 25.
Proof. reflexivity. Qed.

Theorem ortho_z_lines_count : length ortho_z_lines = 25.
Proof. reflexivity. Qed.

Theorem total_ortho_lines_count : length (ortho_x_lines ++ ortho_y_lines ++ ortho_z_lines) = 75.
Proof. reflexivity. Qed.

Theorem diag_xy_lines_count : length diag_xy_lines = 10.
Proof. reflexivity. Qed.

Theorem diag_xz_lines_count : length diag_xz_lines = 10.
Proof. reflexivity. Qed.

Theorem diag_yz_lines_count : length diag_yz_lines = 10.
Proof. reflexivity. Qed.

Theorem total_planar_diag_lines_count : length (diag_xy_lines ++ diag_xz_lines ++ diag_yz_lines) = 30.
Proof. reflexivity. Qed.

Theorem space_diag_lines_count : length space_diag_lines = 4.
Proof. reflexivity. Qed.

Theorem all_lines_count : length all_lines = 109.
Proof. reflexivity. Qed.

(** Every winning line contains exactly 5 cells *)
Theorem all_lines_length_five : forall l : list cell,
  In l all_lines -> length l = 5.
Proof.
  intros l Hl.
  assert (Hcheck : forallb (fun x => length x =? 5) all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck l Hl).
Qed.

Theorem all_lines_cells_valid : forall (l : list cell) (c : cell),
  In l all_lines -> In c l -> c < 125.
Proof.
  intros l c Hl Hc.
  assert (Hcheck : forallb (fun line => forallb (fun x => x <? 125) line) all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  pose proof (Hcheck l Hl) as Hline.
  rewrite forallb_forall in Hline.
  apply Nat.ltb_lt, (Hline c Hc).
Qed.

Definition nodup_cells (l : list cell) : bool :=
  let fix nd (rem : list cell) : bool :=
    match rem with
    | [] => true
    | h :: t => negb (existsb (Nat.eqb h) t) && nd t
    end
  in nd l.

Theorem all_lines_elements_nodup : forall l : list cell,
  In l all_lines -> nodup_cells l = true.
Proof.
  intros l Hl.
  assert (Hcheck : forallb nodup_cells all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply (Hcheck l Hl).
Qed.

Definition line_eqb (l1 l2 : list cell) : bool :=
  forallb (fun c => existsb (Nat.eqb c) l2) l1 && (length l1 =? length l2).

Definition lines_NoDup_bool (ls : list (list cell)) : bool :=
  let fix check (rem : list (list cell)) : bool :=
    match rem with
    | [] => true
    | h :: t => negb (existsb (line_eqb h) t) && check t
    end
  in check ls.

Theorem all_lines_NoDup : lines_NoDup_bool all_lines = true.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 3. CELL DEGREES AND THE INCIDENCE IDENTITY                                 *)
(** ========================================================================= *)

Definition cell_degree (c : cell) : nat :=
  length (filter (fun l => existsb (Nat.eqb c) l) all_lines).

Definition center_cell : cell := 62. (** (2, 2, 2) *)

Theorem center_cell_coords :
  cell_x center_cell = 2 /\ cell_y center_cell = 2 /\ cell_z center_cell = 2.
Proof.
  unfold center_cell, cell_x, cell_y, cell_z.
  repeat split; reflexivity.
Qed.

Theorem center_cell_degree : cell_degree center_cell = 13.
Proof. reflexivity. Qed.

Definition deg13_cells : list cell := filter (fun c => cell_degree c =? 13) all_cells.
Definition deg7_cells  : list cell := filter (fun c => cell_degree c =? 7)  all_cells.
Definition deg5_cells  : list cell := filter (fun c => cell_degree c =? 5)  all_cells.
Definition deg4_cells  : list cell := filter (fun c => cell_degree c =? 4)  all_cells.
Definition deg3_cells  : list cell := filter (fun c => cell_degree c =? 3)  all_cells.

Theorem deg13_cells_count : length deg13_cells = 1.
Proof. reflexivity. Qed.

Theorem deg7_cells_count : length deg7_cells = 16.
Proof. reflexivity. Qed.

Theorem deg5_cells_count : length deg5_cells = 12.
Proof. reflexivity. Qed.

Theorem deg4_cells_count : length deg4_cells = 72.
Proof. reflexivity. Qed.

Theorem deg3_cells_count : length deg3_cells = 24.
Proof. reflexivity. Qed.

Theorem cell_degree_partition_sum :
  length deg13_cells + length deg7_cells + length deg5_cells + length deg4_cells + length deg3_cells = 125.
Proof. reflexivity. Qed.

Theorem total_incidence_identity :
  1 * 13 + 16 * 7 + 12 * 5 + 72 * 4 + 24 * 3 = 109 * 5.
Proof. reflexivity. Qed.
