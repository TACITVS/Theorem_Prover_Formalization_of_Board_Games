(** Generated decoder data. Every claimed game guarantee is checked below.
    The local nonterminal position is not a forced opening strategy. *)
From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SafePairing ZLinearAlgebra ZLinearDefense ZPairingSeparation ZZLinearTrees.
Import ListNotations.

Definition scheduled_white (cells : list cell) : WhiteStrategy :=
  fun st => nth (length (white_stones st)) cells 0.
Definition scheduled_black (cells : list cell) : BlackStrategy :=
  fun st => nth (length (black_stones st)) cells 0.

Lemma prefix_validity : forall n turn st w b,
  n + length (history st) <= 125 -> valid_state st ->
  valid_state (final_state (step_game n turn st w b)).
Proof.
  induction n as [|n IH]; intros turn st w b Hlen Hvalid; [exact Hvalid|].
  rewrite step_game_equation. cbn zeta.
  set (next := move_state turn st (if turn then w st else b st)).
  assert (Hnext : valid_state next) by (apply move_preserves_validity; [exact Hvalid|lia]).
  destruct (move_result turn next); [exact Hnext|].
  apply IH; [unfold next; rewrite move_state_history; lia|exact Hnext].
Qed.

Definition white_history : list cell := [38;5;98;79;4;24;76;39;2;122].
Definition black_history : list cell := [62;83;104;41;100;124;93;31;48;9].
Definition linear_state : GameState := make_state
  [122;2;39;76;24;4;79;98;5;38] [9;48;31;93;124;100;41;104;83;62]
  [9;122;48;2;31;39;93;76;124;24;100;4;41;79;104;98;83;5;62;38].

Theorem linear_state_is_legal_prefix :
  final_state (step_game 20 true initial_state
    (scheduled_white white_history) (scheduled_black black_history)) = linear_state.
Proof. vm_compute. reflexivity. Qed.

Theorem linear_state_valid : valid_state linear_state.
Proof.
  rewrite <- linear_state_is_legal_prefix. apply prefix_validity;
    [cbn; lia|apply initial_state_valid].
Qed.

Theorem linear_state_nonterminal : quiet linear_state.
Proof. vm_compute. split; reflexivity. Qed.

Definition decoder0 : Decoder := [
  (0, 1082369%N);
  (3, 1082378%N);
  (12, 1348672%N);
  (14, 1370176%N);
  (16, 361792%N);
  (17, 1486016%N);
  (19, 1878400%N);
  (21, 2395394%N);
  (22, 4204544%N);
  (23, 9741570%N);
  (29, 1040187392%N);
  (30, 36319350751232%N);
  (32, 86646533061007156371130520801938816%N);
  (34, 580559822651392%N);
  (36, 2596148506638668575444593278978048%N);
  (37, 2596148506638668575444696358193152%N);
  (42, 84050384709110992706503627619206528%N);
  (43, 3713820302323591457398860160%N);
  (51, 85754107032404138002350175429102848%N);
  (52, 86808792333005562918197242724912384%N);
  (53, 1216944577435360671617212808691712%N);
  (55, 1216944577428026081116579547840512%N);
  (56, 85754107032401852981733838882639104%N);
  (57, 86808792333000666600178765894290688%N);
  (69, 1143698132569992200192%N);
  (70, 1216944577429244684244051872972800%N);
  (73, 1216944577445091031878519190716416%N);
  (74, 19461909472914389860352%N);
  (78, 491126114218443102224384%N);
  (81, 81783831696929663668872806400%N);
  (84, 1217045488888800178650774157437952%N);
  (85, 1216944614942542279617157527536640%N);
  (88, 1216945736825702881993031654867968%N);
  (92, 5111494203424727586438129664%N);
  (95, 1216985429449359357249767621035008%N);
  (97, 158456329750895298794221479936%N);
  (99, 1217658868835452970742919878192128%N);
  (101, 85756642333604594458901368954719490%N);
  (102, 86813862935557591558751458691419392%N);
  (103, 1227085782426081157136773257659394%N);
  (105, 1257509395426403566284729579732992%N);
  (110, 2515018790890624112003186985828352%N);
  (112, 7788445519916027631842195569675328%N);
  (113, 11601539144410357541080992443311104%N);
  (114, 20769188053109348603556196477347904%N);
  (115, 41538376106218697207113492463648768%N);
  (117, 250203884332288264119435680252166464%N);
  (118, 333280655113826247814381082316646592%N);
  (119, 664614017699499118420327732000106880%N);
  (120, 1329227997022855913342145158064407552%N);
  (121, 2658456070797996621255263517671722242%N);
  (123, 10634473104278759972645883101142321346%N)
].

Definition decoder1 : Decoder := [
  (1, 11%N);
  (6, 11223104%N);
  (7, 4329600%N);
  (8, 14749952%N);
  (10, 4215808%N);
  (11, 9062409%N);
  (13, 13262857%N);
  (15, 10539009%N);
  (18, 11489281%N);
  (20, 15728640%N);
  (25, 1330584421541241335547368931929903104%N);
  (26, 2535301200456461054793287204873%N);
  (27, 1330571745035541284696998622686892033%N);
  (28, 10141205104057299122830442496008%N);
  (35, 240518168576%N);
  (40, 1356386142245386103014686688563200%N);
  (44, 2041916375410663303911037088114425857%N);
  (45, 1329228035398998310627631758850392064%N);
  (46, 3989028330816621402277737263620182017%N);
  (47, 1330571745035541284697143624943554561%N);
  (49, 2041916375410663303911582463598542849%N);
  (50, 1372122756795438699408541002483367936%N);
  (54, 1372122756795438699409666902390210560%N);
  (58, 25974794974886733816557527594696705%N);
  (59, 25974794974886734212874294803300353%N);
  (60, 1298074253319334287722468442394624%N);
  (61, 245336863415655016310217313794146313%N);
  (63, 10384594026554674301778098251251721%N);
  (64, 1398072198758301407125038347665801217%N);
  (65, 1370824682619491836249088480096833536%N);
  (66, 1573312222337470930745893853675393032%N);
  (67, 166153504424874788828453969854595072%N);
  (68, 36359388382481118853921193286844424%N);
  (71, 1330571903491898189199437444644098049%N);
  (72, 1330571903491871035592160944184119297%N);
  (75, 1330566674432875919251848335980515329%N);
  (77, 1330566674433291487502340864759320577%N);
  (80, 40564820416229196491321769984000%N);
  (82, 171350866938885928081686074751062016%N);
  (86, 207692711268648766152864404647575552%N);
  (87, 1501917704930018287158985415203110913%N);
  (89, 1377303011943132097806862426088947713%N);
  (90, 1330526071276175245323988300088758273%N);
  (91, 207691881769033340853514696703737856%N);
  (94, 1377302397325245405729390005469069313%N);
  (96, 911123868914039882325755428864%N);
  (106, 3900796679913904319074034149738151936%N);
  (107, 171513126210879438022503943687372800%N);
  (108, 10976850218701085859275464369617502208%N);
  (109, 14021206941293595655945507873365164032%N);
  (111, 40240300653644914121111346551455744%N);
  (116, 1287689620916637251875563089646583808%N)
].

Theorem linear_certificate_checks : linear_leafb decoder0 decoder1 linear_state = true.
Proof. vm_compute. reflexivity. Qed.

Theorem linear_state_total_defense : exists b : BlackStrategy, forall w : WhiteStrategy,
  outcome (step_game 105 true linear_state w b) <> WhiteWins.
Proof.
  exact (checked_linear_leaf_total_defense decoder0 decoder1 linear_state 105
    linear_certificate_checks linear_state_valid eq_refl).
Qed.

Theorem information_set_sizes :
  length (decoder_cells decoder0) = 52 /\ length (decoder_cells decoder1) = 52.
Proof. split; reflexivity. Qed.

Theorem pair_capacity_fails :
  length (residual_rows linear_state) = 53 /\
  length (filter (is_legal_move linear_state) all_cells) = 105 /\
  2 * length (residual_rows linear_state) > length (filter (is_legal_move linear_state) all_cells).
Proof. vm_compute. repeat split; lia. Qed.

Theorem no_static_pairing_defense_exists : forall mate,
  well_mated mate -> ~ pairing_safe mate linear_state.
Proof.
  intros mate Hmate Hsafe.
  pose proof (every_static_pairing_needs_capacity linear_state mate Hmate Hsafe) as Hcapacity.
  assert (Hlines : length (unblocked_lines linear_state) = 53) by (vm_compute; reflexivity).
  assert (Hfree : length (empty_cells linear_state) = 105) by (vm_compute; reflexivity).
  rewrite Hlines, Hfree in Hcapacity. lia.
Qed.

Theorem linear_defense_strictly_beyond_pairing :
  (exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game 105 true linear_state w b) <> WhiteWins) /\
  (forall mate, well_mated mate -> ~ pairing_safe mate linear_state).
Proof. split; [exact linear_state_total_defense|exact no_static_pairing_defense_exists]. Qed.

Definition local_linear_tree : LinearDefenseCertificate := LinearLeaf decoder0 decoder1.

Theorem local_linear_tree_checks : linear_treeb local_linear_tree linear_state = true.
Proof. exact linear_certificate_checks. Qed.

Theorem local_linear_tree_does_not_check_empty : linear_treeb local_linear_tree initial_state = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions linear_state_total_defense.
Print Assumptions pair_capacity_fails.
Print Assumptions linear_defense_strictly_beyond_pairing.
