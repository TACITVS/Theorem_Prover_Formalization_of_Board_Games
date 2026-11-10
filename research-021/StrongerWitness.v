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

Definition white_history : list cell := [67;124;48;87;16;39;121;97;63;119;60].
Definition black_history : list cell := [62;91;41;120;100;104;31;81;24;4;20].
Definition linear_state : GameState := make_state
  [60;119;63;97;121;39;16;87;48;124;67] [20;4;24;81;31;104;100;120;41;91;62]
  [20;60;4;119;24;63;81;97;31;121;104;39;100;16;120;87;41;48;91;124;62;67].

Theorem linear_state_is_legal_prefix :
  final_state (step_game 22 true initial_state
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
  (5, 1216944577428027125915375894528032%N);
  (7, 243388945466965751625905340416192%N);
  (8, 324518563329833571930574159872256%N);
  (9, 649037126659667143861148319744512%N);
  (11, 79228164875447649397110736962%N);
  (14, 79228164875447649397110764610%N);
  (18, 324845379509649645288878229430272%N);
  (19, 324845379509649645288878229856256%N);
  (21, 79228164875447649397112832000%N);
  (22, 243388945466965751625905344745540%N);
  (23, 326816179816073358321257545736%N);
  (27, 81129673473455522722929061134400%N);
  (28, 81129673473455523303454255611968%N);
  (29, 580559856205824%N);
  (32, 81129673473455522577660248064064%N);
  (35, 309485305257480864747487232%N);
  (38, 309485305257480899107225600%N);
  (40, 309485305258255987192627200%N);
  (43, 81129982958760780792865719582784%N);
  (45, 809240558043136%N);
  (51, 2596227734801254395295235043229762%N);
  (52, 5319751599819934017391378350387367942%N);
  (53, 9740178108494049705984%N);
  (54, 5317155372085142650756025498418155588%N);
  (55, 1116892707587883008%N);
  (61, 2596227734803544023093990389710914%N);
  (69, 996124179980315787264%N);
  (70, 1218567098675306168320%N);
  (72, 5317155372085135179733477753595498564%N);
  (74, 5317155372085161190292265930311471172%N);
  (76, 83157958680581247180687831728128064%N);
  (77, 83482716099933003603333125953986624%N);
  (78, 327135629019173558332784902144%N);
  (79, 324609341012795017843889917829120%N);
  (85, 40891953627396694791598112768%N);
  (89, 41859094283088398131363053568%N);
  (92, 83482721056377748295860913602469952%N);
  (94, 324865186550684039760490411499520%N);
  (99, 1069580193942568557512843329536%N);
  (101, 85756563105439719011251971843686400%N);
  (102, 5403158256858314769214424335394058242%N);
  (103, 91597994268996132437331103711304%N);
  (105, 1257509395426403566284729579732992%N);
  (110, 1298115377387013333640112477570048%N);
  (112, 7788524593338387792525688653746242%N);
  (113, 10384593717069950693196548162985984%N);
  (114, 20769307902428467854223450050671682%N);
  (115, 41538376415704002465367280633020416%N);
  (117, 249636215577732075267320094587396160%N);
  (118, 332712964385833955530782515281272896%N);
  (123, 10633823976182847297513498690025685000%N)
].

Definition decoder1 : Decoder := [
  (1, 2100130%N);
  (2, 5070602552028649561415221248004%N);
  (3, 10141205104057299122830442496008%N);
  (6, 992%N);
  (10, 1298074253319333134800792032642048%N);
  (12, 1308215458423390433923622483810560%N);
  (13, 10141205104057299122830451155200%N);
  (15, 1313286060975419083485037709543808%N);
  (17, 1313286060975419083485037709379968%N);
  (25, 2535301276014324780708518693792%N);
  (26, 2535301276014324780707612724128%N);
  (30, 2535301276014324817027802336160%N);
  (33, 9079829299200%N);
  (34, 10868829299657088221615165565449536128%N);
  (36, 27269700370067550525109560030791936%N);
  (37, 27269700370067550525109388232100096%N);
  (42, 167466790485850060337986417887299968%N);
  (44, 19807041218861912349278208000%N);
  (46, 10676719361115777998593344288638648832%N);
  (47, 192120059939070829995384767315460224%N);
  (49, 10868829279850047002753833741668844160%N);
  (50, 34902897112121344%N);
  (56, 10976515558942649811278141620465172736%N);
  (57, 20769188053114054977756789328592896%N);
  (58, 10976515558942625607001699891277725952%N);
  (59, 20769188053128810513029110865870848%N);
  (64, 20769188053109348603556196476010496%N);
  (65, 1217554914659054649344%N);
  (66, 10966141106430661853481730119034994688%N);
  (68, 10966141106430660303903436531717898240%N);
  (71, 10394734922200866154453124314824960%N);
  (73, 10394734922183157280142363145273600%N);
  (75, 1171146887751672012996608%N);
  (80, 43100121692243521308347424836480%N);
  (82, 4956746976147431444942159872%N);
  (83, 10141214473232392137803124703232%N);
  (84, 654271258038347116665569804288%N);
  (86, 10394735657200610881878636208849152%N);
  (88, 10394735231658722377529166712275200%N);
  (90, 42851662167195260031515296625346944%N);
  (93, 10633834117387951354812630582580740096%N);
  (95, 42894800625209727139491855267807744%N);
  (96, 10687093892856488142493570559229313792%N);
  (98, 10644219018114150752834983480265015552%N);
  (106, 577726690451614636814516499037290496%N);
  (107, 20931452281854541066006111801327744%N);
  (108, 10976850218701085859275464369617502208%N);
  (109, 10848708495697301079184261177873023104%N);
  (111, 40240300653644914121111346551455744%N);
  (116, 623075623024179315423659559506411520%N);
  (122, 5509032043078739043976955140589502592%N)
].

Theorem linear_certificate_checks : linear_leafb decoder0 decoder1 linear_state = true.
Proof. vm_compute. reflexivity. Qed.

Theorem linear_state_total_defense : exists b : BlackStrategy, forall w : WhiteStrategy,
  outcome (step_game 103 true linear_state w b) <> WhiteWins.
Proof.
  exact (checked_linear_leaf_total_defense decoder0 decoder1 linear_state 103
    linear_certificate_checks linear_state_valid eq_refl).
Qed.

Theorem information_set_sizes :
  length (decoder_cells decoder0) = 51 /\ length (decoder_cells decoder1) = 51.
Proof. split; reflexivity. Qed.

Theorem pair_capacity_fails :
  length (residual_rows linear_state) = 54 /\
  length (filter (is_legal_move linear_state) all_cells) = 103 /\
  2 * length (residual_rows linear_state) > length (filter (is_legal_move linear_state) all_cells).
Proof. vm_compute. repeat split; lia. Qed.

Theorem no_static_pairing_defense_exists : forall mate,
  well_mated mate -> ~ pairing_safe mate linear_state.
Proof.
  intros mate Hmate Hsafe.
  pose proof (every_static_pairing_needs_capacity linear_state mate Hmate Hsafe) as Hcapacity.
  assert (Hlines : length (unblocked_lines linear_state) = 54) by (vm_compute; reflexivity).
  assert (Hfree : length (empty_cells linear_state) = 103) by (vm_compute; reflexivity).
  rewrite Hlines, Hfree in Hcapacity. lia.
Qed.

Theorem linear_defense_strictly_beyond_pairing :
  (exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (step_game 103 true linear_state w b) <> WhiteWins) /\
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
