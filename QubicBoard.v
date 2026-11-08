(** QubicBoard.v: 4x4x4 3D Tic-Tac-Toe Geometry, 76 Winning Lines, and O_h Symmetry Orbits in Rocq 9.1 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. COORDINATES AND 64-CELL GRID                                            *)
(** ========================================================================= *)

Definition cell := nat.

Definition cell_x (c : cell) : nat := c mod 4.
Definition cell_y (c : cell) : nat := (c / 4) mod 4.
Definition cell_z (c : cell) : nat := c / 16.

Definition make_cell (x y z : nat) : cell := 16 * z + 4 * y + x.

Definition all_cells : list cell := seq 0 64.

Theorem all_cells_length : length all_cells = 64.
Proof. reflexivity. Qed.

Theorem all_cells_NoDup : NoDup all_cells.
Proof. apply seq_NoDup. Qed.

Lemma make_cell_decomp : forall x y z : nat,
  x < 4 -> y < 4 -> z < 4 ->
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
  x < 4 -> y < 4 -> z < 4 ->
  make_cell x y z < 64.
Proof.
  intros x y z Hx Hy Hz.
  unfold make_cell. lia.
Qed.

(** ========================================================================= *)
(** 2. ENUMERATION OF ALL 76 WINNING LINES                                      *)
(** ========================================================================= *)

(** 16 Orthogonal X-lines (varying x in 0..3) *)
Definition ortho_x_lines : list (list cell) :=
  [ [0; 1; 2; 3];     [4; 5; 6; 7];     [8; 9; 10; 11];   [12; 13; 14; 15];
    [16; 17; 18; 19]; [20; 21; 22; 23]; [24; 25; 26; 27]; [28; 29; 30; 31];
    [32; 33; 34; 35]; [36; 37; 38; 39]; [40; 41; 42; 43]; [44; 45; 46; 47];
    [48; 49; 50; 51]; [52; 53; 54; 55]; [56; 57; 58; 59]; [60; 61; 62; 63] ].

(** 16 Orthogonal Y-lines (varying y in 0..3) *)
Definition ortho_y_lines : list (list cell) :=
  [ [0; 4; 8; 12];    [1; 5; 9; 13];    [2; 6; 10; 14];   [3; 7; 11; 15];
    [16; 20; 24; 28]; [17; 21; 25; 29]; [18; 22; 26; 30]; [19; 23; 27; 31];
    [32; 36; 40; 44]; [33; 37; 41; 45]; [34; 38; 42; 46]; [35; 39; 43; 47];
    [48; 52; 56; 60]; [49; 53; 57; 61]; [50; 54; 58; 62]; [51; 55; 59; 63] ].

(** 16 Orthogonal Z-lines (varying z in 0..3) *)
Definition ortho_z_lines : list (list cell) :=
  [ [0; 16; 32; 48];  [1; 17; 33; 49];  [2; 18; 34; 50];  [3; 19; 35; 51];
    [4; 20; 36; 52];  [5; 21; 37; 53];  [6; 22; 38; 54];  [7; 23; 39; 55];
    [8; 24; 40; 56];  [9; 25; 41; 57];  [10; 26; 42; 58]; [11; 27; 43; 59];
    [12; 28; 44; 60]; [13; 29; 45; 61]; [14; 30; 46; 62]; [15; 31; 47; 63] ].

(** 8 Planar Diagonals in XY-planes (z in 0..3) *)
Definition diag_xy_lines : list (list cell) :=
  [ [0; 5; 10; 15];   [3; 6; 9; 12];
    [16; 21; 26; 31]; [19; 22; 25; 28];
    [32; 37; 42; 47]; [35; 38; 41; 44];
    [48; 53; 58; 63]; [51; 54; 57; 60] ].

(** 8 Planar Diagonals in XZ-planes (y in 0..3) *)
Definition diag_xz_lines : list (list cell) :=
  [ [0; 17; 34; 51];  [48; 33; 18; 3];
    [4; 21; 38; 55];  [52; 37; 22; 7];
    [8; 25; 42; 59];  [56; 41; 26; 11];
    [12; 29; 46; 63]; [60; 45; 30; 15] ].

(** 8 Planar Diagonals in YZ-planes (x in 0..3) *)
Definition diag_yz_lines : list (list cell) :=
  [ [0; 20; 40; 60];  [48; 36; 24; 12];
    [1; 21; 41; 61];  [49; 37; 25; 13];
    [2; 22; 42; 62];  [50; 38; 26; 14];
    [3; 23; 43; 63];  [51; 39; 27; 15] ].

(** 4 3D Space Diagonals (Triagonals through opposite corners) *)
Definition space_diag_lines : list (list cell) :=
  [ [0; 21; 42; 63];
    [3; 22; 41; 60];
    [12; 25; 38; 51];
    [48; 37; 26; 15] ].

(** The Master Set of All 76 Winning Lines *)
Definition all_lines : list (list cell) :=
  ortho_x_lines ++ ortho_y_lines ++ ortho_z_lines ++
  diag_xy_lines ++ diag_xz_lines ++ diag_yz_lines ++
  space_diag_lines.

Theorem ortho_x_lines_count : length ortho_x_lines = 16.
Proof. reflexivity. Qed.

Theorem ortho_y_lines_count : length ortho_y_lines = 16.
Proof. reflexivity. Qed.

Theorem ortho_z_lines_count : length ortho_z_lines = 16.
Proof. reflexivity. Qed.

Theorem total_ortho_lines_count : length (ortho_x_lines ++ ortho_y_lines ++ ortho_z_lines) = 48.
Proof. reflexivity. Qed.

Theorem diag_xy_lines_count : length diag_xy_lines = 8.
Proof. reflexivity. Qed.

Theorem diag_xz_lines_count : length diag_xz_lines = 8.
Proof. reflexivity. Qed.

Theorem diag_yz_lines_count : length diag_yz_lines = 8.
Proof. reflexivity. Qed.

Theorem total_planar_diag_lines_count : length (diag_xy_lines ++ diag_xz_lines ++ diag_yz_lines) = 24.
Proof. reflexivity. Qed.

Theorem space_diag_lines_count : length space_diag_lines = 4.
Proof. reflexivity. Qed.

Theorem all_lines_count : length all_lines = 76.
Proof. reflexivity. Qed.

(** Every winning line contains exactly 4 cells *)
Theorem all_lines_length_four : forall l : list cell,
  In l all_lines -> length l = 4.
Proof.
  intros l Hl.
  assert (Hcheck : forallb (fun x => length x =? 4) all_lines = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck l Hl).
Qed.

Theorem all_lines_cells_valid : forall (l : list cell) (c : cell),
  In l all_lines -> In c l -> c < 64.
Proof.
  intros l c Hl Hc.
  assert (Hcheck : forallb (fun line => forallb (fun x => x <? 64) line) all_lines = true) by reflexivity.
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

(** Boolean uniqueness check for all 76 lines *)
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
(** 3. HYPEROCTAHEDRAL SYMMETRY ORBITS (O_h)                                   *)
(** ========================================================================= *)

Definition is_corner_val (v : nat) : bool := (v =? 0) || (v =? 3).

Definition count_corner_coords (c : cell) : nat :=
  (if is_corner_val (cell_x c) then 1 else 0) +
  (if is_corner_val (cell_y c) then 1 else 0) +
  (if is_corner_val (cell_z c) then 1 else 0).

Definition is_corner (c : cell) : bool := count_corner_coords c =? 3.
Definition is_edge (c : cell) : bool := count_corner_coords c =? 2.
Definition is_face (c : cell) : bool := count_corner_coords c =? 1.
Definition is_cube (c : cell) : bool := count_corner_coords c =? 0.

Definition corners : list cell := filter is_corner all_cells.
Definition edges : list cell := filter is_edge all_cells.
Definition faces : list cell := filter is_face all_cells.
Definition cube_centers : list cell := filter is_cube all_cells.

Theorem corners_count : length corners = 8.
Proof. reflexivity. Qed.

Theorem edges_count : length edges = 24.
Proof. reflexivity. Qed.

Theorem faces_count : length faces = 24.
Proof. reflexivity. Qed.

Theorem cube_centers_count : length cube_centers = 8.
Proof. reflexivity. Qed.

Theorem cell_partition_sum : length corners + length edges + length faces + length cube_centers = 64.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 4. CELL DEGREES AND THE INCIDENCE IDENTITY                                 *)
(** ========================================================================= *)

Definition cell_degree (c : cell) : nat :=
  length (filter (fun l => existsb (Nat.eqb c) l) all_lines).

Theorem corner_degree_uniform : forallb (fun c => cell_degree c =? 7) corners = true.
Proof. reflexivity. Qed.

Theorem edge_degree_uniform : forallb (fun c => cell_degree c =? 4) edges = true.
Proof. reflexivity. Qed.

Theorem face_degree_uniform : forallb (fun c => cell_degree c =? 4) faces = true.
Proof. reflexivity. Qed.

Theorem cube_center_degree_uniform : forallb (fun c => cell_degree c =? 7) cube_centers = true.
Proof. reflexivity. Qed.

Theorem corner_degree_all : forall c : cell,
  In c corners -> cell_degree c = 7.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x =? 7) corners = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck c Hc).
Qed.

Theorem edge_degree_all : forall c : cell,
  In c edges -> cell_degree c = 4.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x =? 4) edges = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck c Hc).
Qed.

Theorem face_degree_all : forall c : cell,
  In c faces -> cell_degree c = 4.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x =? 4) faces = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck c Hc).
Qed.

Theorem cube_center_degree_all : forall c : cell,
  In c cube_centers -> cell_degree c = 7.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun x => cell_degree x =? 7) cube_centers = true) by reflexivity.
  rewrite forallb_forall in Hcheck.
  apply Nat.eqb_eq, (Hcheck c Hc).
Qed.

Theorem total_incidence_identity :
  8 * 7 + 24 * 4 + 24 * 4 + 8 * 7 = 76 * 4.
Proof. reflexivity. Qed.
