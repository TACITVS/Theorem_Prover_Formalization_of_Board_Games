(** Exact executable regressions against the locked Rules.play, not a separate
    simulator. Concrete plays establish examples, never minimax conclusions. *)
From Stdlib Require Import List Arith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Solution.
Import ListNotations.

Definition line_attack : WhiteStrategy := fun st => length (white_stones st).

Theorem pairing_policy_loses_on_ply_nine :
  outcome (play line_attack Solution.black_pairing_policy) = WhiteWins /\
  length (history (final_state (play line_attack Solution.black_pairing_policy))) = 9.
Proof. vm_compute. split; reflexivity. Qed.

Theorem pairing_policy_is_not_nonlosing :
  ~ (forall w, outcome (play w Solution.black_pairing_policy) <> WhiteWins).
Proof.
  intros H. apply (H line_attack). exact (proj1 pairing_policy_loses_on_ply_nine).
Qed.

Definition white_decoys : WhiteStrategy := fun st => 5 + 2 * length (white_stones st).
Definition black_attack : BlackStrategy := fun st => length (black_stones st).

Theorem black_win_stops_on_ply_ten :
  outcome (play white_decoys black_attack) = BlackWins /\
  length (history (final_state (play white_decoys black_attack))) = 10.
Proof. vm_compute. split; reflexivity. Qed.

Definition draw_white_cells : list cell :=
  [0;7;13;14;15;17;20;21;22;23;26;28;29;30;31;33;35;37;38;42;45;46;48;
   51;59;61;62;63;65;66;69;72;73;74;75;76;77;79;80;82;86;87;90;93;94;97;
   99;101;103;104;105;107;108;109;112;114;115;116;118;119;121;122;123].

Definition draw_black_cells : list cell :=
  [1;2;3;4;5;6;8;9;10;11;12;16;18;19;24;25;27;32;34;36;39;40;41;43;44;
   47;49;50;52;53;54;55;56;57;58;60;64;67;68;70;71;78;81;83;84;85;88;89;
   91;92;95;96;98;100;102;106;110;111;113;117;120;124].

Definition scheduled_white (cells : list cell) : WhiteStrategy :=
  fun st => nth (length (white_stones st)) cells 0.
Definition scheduled_black (cells : list cell) : BlackStrategy :=
  fun st => nth (length (black_stones st)) cells 0.

Theorem concrete_full_board_draw :
  let tr := play (scheduled_white draw_white_cells) (scheduled_black draw_black_cells) in
  outcome tr = Draw /\ length (history (final_state tr)) = 125.
Proof. vm_compute. split; reflexivity. Qed.

(** Change ownership of 13 and 1 in the draw coloring, playing 1 last.
    The only monochromatic line is [1;26;51;76;101], completed on ply 125. *)
Definition final_win_white_cells : list cell :=
  [0;7;14;15;17;20;21;22;23;26;28;29;30;31;33;35;37;38;42;45;46;48;
   51;59;61;62;63;65;66;69;72;73;74;75;76;77;79;80;82;86;87;90;93;94;97;
   99;101;103;104;105;107;108;109;112;114;115;116;118;119;121;122;123;1].

Definition final_win_black_cells : list cell :=
  [2;3;4;5;6;8;9;10;11;12;13;16;18;19;24;25;27;32;34;36;39;40;41;43;44;
   47;49;50;52;53;54;55;56;57;58;60;64;67;68;70;71;78;81;83;84;85;88;89;
   91;92;95;96;98;100;102;106;110;111;113;117;120;124].

Theorem last_ply_win_takes_precedence_over_draw :
  let tr := play (scheduled_white final_win_white_cells) (scheduled_black final_win_black_cells) in
  outcome tr = WhiteWins /\ length (history (final_state tr)) = 125.
Proof. vm_compute. split; reflexivity. Qed.
