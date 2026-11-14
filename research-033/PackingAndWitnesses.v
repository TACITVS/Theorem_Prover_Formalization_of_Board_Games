(** Packing Refutations, Phi-Soundness Counterexample, and Real Engine Separation Witnesses:
    1) Formal refutation of `5x5x5_QUBIC_HandOff_b.md` line 84 (`13` residual pairs
       in the `27` unused cells -> `83/109`): exact Hall obstruction bounds residual
       pairs to `<= 9` (`<= 79/109`), and uncoordinated per-Slice-14 defense loses in
       5 moves at Move 0.
    2) Constructive counterexample to `5x5x5_QUBIC_HandOff.md` (`Phi < 1.0` without
       `+ max_x D(x)`): a balanced 54-ply reachable legal board with global potential
       `phi = 16 < 32` (`Phi = 0.5 < 1.0`) and NO Black 4-in-a-rows, from which White
       forces `WhiteWins` in 2 moves against EVERY `BlackStrategy`.
    3) Strict separation witnesses from real benchmark games (`research-032/mb_equal.jsonl`
       `id=0` at `ply 26`, and `research-029/games_cert.jsonl` `id=15` at `ply 24`):
       static pairing is impossible (`2 * alive > empty`), yet `hybrid_certificateb`
       certifies Black non-loss via `vm_compute` + `ExactRegionCertificates`. *)

From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts.
From QubicResearch033 Require Import ExactRegionCertificates GadgetCatalog.
Import ListNotations.

(** ** 1. Replay and Table-Lookup Infrastructure *)

Fixpoint replay_moves (st : GameState) (turn_w : bool) (ms : list cell) : GameState :=
  match ms with
  | [] => st
  | c :: rest => replay_moves (move_state turn_w st c) (negb turn_w) rest
  end.

Lemma replay_moves_valid st turn_w ms :
  valid_state st ->
  length (history st) + length ms <= 125 ->
  Forall (fun c => c < 125 /\ occupied st c = false) ms ->
  NoDup ms ->
  valid_state (replay_moves st turn_w ms) /\ length (history (replay_moves st turn_w ms)) = length (history st) + length ms.
Proof.
  revert st turn_w. induction ms as [|a rest IH]; intros st turn_w Hval Hlen Hall Hnd; simpl.
  - split; [exact Hval|lia].
  - inversion Hall as [|? ? [Ha1 Ha2] Hrest]; subst.
    inversion Hnd as [|? ? Hnain Hnd_r]; subst.
    assert (Hlt : length (history st) < 125) by (simpl in Hlen; lia).
    assert (Hleg : is_legal_move st a = true).
    { unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt, Ha1|rewrite Ha2; reflexivity]. }
    assert (Heff : effective_move st a = a) by (apply effective_legal, Hleg).
    assert (Hval1 : valid_state (move_state turn_w st a))
      by (apply move_preserves_validity; assumption).
    assert (Hlen1 : length (history (move_state turn_w st a)) = S (length (history st)))
      by (apply move_state_history).
    assert (Hrest1 : Forall (fun c => c < 125 /\ occupied (move_state turn_w st a) c = false) rest).
    { rewrite Forall_forall in Hrest |- *. intros c Hcin.
      destruct (Hrest c Hcin) as [Hc1 Hc2]. split; [exact Hc1|].
      assert (Hne : c <> a) by (intros ->; contradiction).
      destruct turn_w.
      - unfold occupied, move_state in *. cbn [white_stones black_stones] in *.
        rewrite Heff. unfold occupied in Hc2. apply orb_false_iff in Hc2 as [Hw Hb].
        apply orb_false_iff. split; [simpl; rewrite (proj2 (Nat.eqb_neq c a) Hne); exact Hw|exact Hb].
      - unfold occupied, move_state in *. cbn [white_stones black_stones] in *.
        rewrite Heff. unfold occupied in Hc2. apply orb_false_iff in Hc2 as [Hw Hb].
        apply orb_false_iff. split; [exact Hw|simpl; rewrite (proj2 (Nat.eqb_neq c a) Hne); exact Hb]. }
    destruct (IH (move_state turn_w st a) (negb turn_w) Hval1 ltac:(simpl in Hlen; lia) Hrest1 Hnd_r)
      as [Hv Hl].
    split; [exact Hv|lia].
Qed.

Lemma replay_initial_valid ms :
  length ms <= 125 ->
  forallb (fun c => c <? 125) ms = true ->
  nodupb Nat.eqb ms = true ->
  valid_state (replay_moves initial_state true ms) /\ length (history (replay_moves initial_state true ms)) = length ms.
Proof.
  intros Hlen Hlt Hnd.
  apply replay_moves_valid; [apply initial_state_valid|exact Hlen| |apply nat_nodupb_sound, Hnd].
  rewrite Forall_forall. intros c Hc. rewrite forallb_forall in Hlt.
  split; [apply Nat.ltb_lt, Hlt, Hc|reflexivity].
Qed.

Definition table_reg (tbl : list nat) (d : nat) (c : cell) : nat := nth c tbl d.

Definition bucket_asg (buckets : list (list (nat * nat))) (d : nat) (l : list cell) : nat :=
  let c0 := nth 0 l 0 in
  let c1 := nth 1 l 0 in
  match find (fun p => fst p =? c1) (nth c0 buckets []) with
  | Some (_, r) => r
  | None => d
  end.

Definition alive_lines_of (st : GameState) : list (list cell) :=
  filter (fun l => negb (existsb (fun c => mem c (black_stones st)) l)) all_lines.

Definition empty_cells_of (st : GameState) : list cell :=
  filter (fun c => negb (occupied st c)) all_cells.

Record ValidPairing (alines : list (list cell)) (ecells : list cell) := mk_valid_pairing {
  vp_pairs : list (list cell * (cell * cell));
  vp_lines_nodup : NoDup (map fst vp_pairs);
  vp_covers_all : forall l, In l alines -> In l (map fst vp_pairs);
  vp_pairs_ok : forall l a b, In (l, (a, b)) vp_pairs ->
    a <> b /\ In a l /\ In b l /\ In a ecells /\ In b ecells;
  vp_cells_nodup : NoDup (flat_map (fun '(_, (a, b)) => [a; b]) vp_pairs)
}.

Lemma no_pairing_when_deficit alines ecells :
  NoDup alines ->
  length ecells < 2 * length alines ->
  ValidPairing alines ecells -> False.
Proof.
  intros Hnda Hdef [ps _ Hcov Hok Hndc].
  assert (Hle1 : length alines <= length ps).
  { rewrite <- (length_map fst ps). apply NoDup_incl_length; assumption. }
  assert (Hflat_len : length (flat_map (fun '(_, (a, b)) => [a; b]) ps) = 2 * length ps).
  { clear. induction ps as [|[l [a b]] t IH]; simpl; [lia|lia]. }
  assert (Hle2 : 2 * length ps <= length ecells).
  { rewrite <- Hflat_len. apply NoDup_incl_length; [exact Hndc|].
    intros c Hc. apply in_flat_map in Hc as [[l [a b]] [Hp Hcab]].
    destruct (Hok l a b Hp) as (_ & _ & _ & Ha & Hb).
    simpl in Hcab. destruct Hcab as [<-|[<-|[]]]; assumption. }
  lia.
Qed.

(** ** 2. Audit of 7-Slice-14 Packing (`HandOff_b.md` Line 84) & Move-0 Loss *)
Definition pack7_cells : list cell := [
  0; 2; 3; 4; 6; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19;
  20; 21; 22; 23; 24; 25; 28; 29; 31; 32; 33; 34; 36; 38; 39;
  40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 53; 54; 56; 58;
  59; 65; 66; 68; 69; 70; 71; 73; 74; 75; 77; 78; 79; 81; 82;
  83; 84; 85; 86; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98;
  99; 100; 102; 103; 104; 106; 107; 108; 109; 110; 111; 113; 114; 115; 116;
  117; 118; 119; 120; 121; 122; 123; 124
].
Definition pack7_lines : list (list cell) := [
  [0; 1; 2; 3; 4];
  [5; 6; 7; 8; 9];
  [10; 11; 12; 13; 14];
  [15; 16; 17; 18; 19];
  [20; 21; 22; 23; 24];
  [25; 26; 27; 28; 29];
  [30; 31; 32; 33; 34];
  [35; 36; 37; 38; 39];
  [40; 41; 42; 43; 44];
  [45; 46; 47; 48; 49];
  [50; 51; 52; 53; 54];
  [55; 56; 57; 58; 59];
  [65; 66; 67; 68; 69];
  [70; 71; 72; 73; 74];
  [75; 76; 77; 78; 79];
  [80; 81; 82; 83; 84];
  [85; 86; 87; 88; 89];
  [90; 91; 92; 93; 94];
  [95; 96; 97; 98; 99];
  [100; 101; 102; 103; 104];
  [105; 106; 107; 108; 109];
  [110; 111; 112; 113; 114];
  [115; 116; 117; 118; 119];
  [120; 121; 122; 123; 124];
  [0; 5; 10; 15; 20];
  [1; 6; 11; 16; 21];
  [2; 7; 12; 17; 22];
  [3; 8; 13; 18; 23];
  [4; 9; 14; 19; 24];
  [25; 30; 35; 40; 45];
  [26; 31; 36; 41; 46];
  [27; 32; 37; 42; 47];
  [28; 33; 38; 43; 48];
  [29; 34; 39; 44; 49];
  [50; 55; 60; 65; 70];
  [51; 56; 61; 66; 71];
  [53; 58; 63; 68; 73];
  [54; 59; 64; 69; 74];
  [75; 80; 85; 90; 95];
  [76; 81; 86; 91; 96];
  [77; 82; 87; 92; 97];
  [78; 83; 88; 93; 98];
  [79; 84; 89; 94; 99];
  [100; 105; 110; 115; 120];
  [101; 106; 111; 116; 121];
  [102; 107; 112; 117; 122];
  [103; 108; 113; 118; 123];
  [104; 109; 114; 119; 124];
  [2; 27; 52; 77; 102];
  [7; 32; 57; 82; 107];
  [10; 35; 60; 85; 110];
  [11; 36; 61; 86; 111];
  [13; 38; 63; 88; 113];
  [14; 39; 64; 89; 114];
  [17; 42; 67; 92; 117];
  [22; 47; 72; 97; 122];
  [0; 6; 12; 18; 24];
  [4; 8; 12; 16; 20];
  [25; 31; 37; 43; 49];
  [29; 33; 37; 41; 45];
  [50; 56; 62; 68; 74];
  [54; 58; 62; 66; 70];
  [75; 81; 87; 93; 99];
  [79; 83; 87; 91; 95];
  [100; 106; 112; 118; 124];
  [104; 108; 112; 116; 120];
  [10; 36; 62; 88; 114];
  [14; 38; 62; 86; 110];
  [2; 32; 62; 92; 122];
  [22; 42; 62; 82; 102]
].
Definition pack7_unused : list cell := [
  1; 5; 7; 11; 12; 26; 27; 30; 35; 37; 51; 52; 55; 57; 60;
  61; 62; 63; 64; 67; 72; 76; 80; 87; 101; 105; 112
].
Definition pack7_uncovered : list (list cell) := [
  [60; 61; 62; 63; 64];
  [52; 57; 62; 67; 72];
  [0; 25; 50; 75; 100];
  [1; 26; 51; 76; 101];
  [3; 28; 53; 78; 103];
  [4; 29; 54; 79; 104];
  [5; 30; 55; 80; 105];
  [6; 31; 56; 81; 106];
  [8; 33; 58; 83; 108];
  [9; 34; 59; 84; 109];
  [12; 37; 62; 87; 112];
  [15; 40; 65; 90; 115];
  [16; 41; 66; 91; 116];
  [18; 43; 68; 93; 118];
  [19; 44; 69; 94; 119];
  [20; 45; 70; 95; 120];
  [21; 46; 71; 96; 121];
  [23; 48; 73; 98; 123];
  [24; 49; 74; 99; 124];
  [0; 26; 52; 78; 104];
  [4; 28; 52; 76; 100];
  [5; 31; 57; 83; 109];
  [9; 33; 57; 81; 105];
  [15; 41; 67; 93; 119];
  [19; 43; 67; 91; 115];
  [20; 46; 72; 98; 124];
  [24; 48; 72; 96; 120];
  [0; 30; 60; 90; 120];
  [20; 40; 60; 80; 100];
  [1; 31; 61; 91; 121];
  [21; 41; 61; 81; 101];
  [3; 33; 63; 93; 123];
  [23; 43; 63; 83; 103];
  [4; 34; 64; 94; 124];
  [24; 44; 64; 84; 104];
  [0; 31; 62; 93; 124];
  [4; 33; 62; 91; 120];
  [20; 41; 62; 83; 104];
  [24; 43; 62; 81; 100]
].
Definition pack7_ge2 : list (list cell) := [
  [60; 61; 62; 63; 64];
  [52; 57; 62; 67; 72];
  [1; 26; 51; 76; 101];
  [5; 30; 55; 80; 105];
  [12; 37; 62; 87; 112];
  [0; 26; 52; 78; 104];
  [4; 28; 52; 76; 100];
  [5; 31; 57; 83; 109];
  [9; 33; 57; 81; 105];
  [0; 30; 60; 90; 120];
  [20; 40; 60; 80; 100];
  [1; 31; 61; 91; 121];
  [21; 41; 61; 81; 101]
].
Definition pack7_conflict_pairs : list (cell * list cell * list cell) := [
  (52, [0; 26; 52; 78; 104], [4; 28; 52; 76; 100]);
  (57, [5; 31; 57; 83; 109], [9; 33; 57; 81; 105]);
  (60, [0; 30; 60; 90; 120], [20; 40; 60; 80; 100]);
  (61, [1; 31; 61; 91; 121], [21; 41; 61; 81; 101])
].
Definition pack7_singletons : list (list cell) := [
  [60; 61; 62; 63; 64];
  [52; 57; 62; 67; 72];
  [1; 26; 51; 76; 101];
  [5; 30; 55; 80; 105];
  [12; 37; 62; 87; 112]
].

Theorem pack7_exact_counts :
  length pack7_cells = 98 /\
  length pack7_lines = 70 /\
  length pack7_unused = 27 /\
  length pack7_uncovered = 39 /\
  length (filter (fun l => length (filter (fun c => mem c pack7_unused) l) =? 0) pack7_uncovered) = 14 /\
  length (filter (fun l => length (filter (fun c => mem c pack7_unused) l) =? 1) pack7_uncovered) = 12 /\
  length pack7_ge2 = 13.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma pack7_ge2_spec_b :
  (forallb (fun '(bc, l1, l2) =>
     negb (list_nat_eqb l1 l2) &&
     mem bc (filter (fun c => mem c pack7_unused) l1) &&
     (length (filter (fun c => mem c pack7_unused) l1) =? 2) &&
     mem bc (filter (fun c => mem c pack7_unused) l2) &&
     (length (filter (fun c => mem c pack7_unused) l2) =? 2))
     pack7_conflict_pairs) &&
  forallb (fun l =>
     if 2 <=? length (filter (fun c => mem c pack7_unused) l)
     then existsb (fun x => list_nat_eqb l x)
                  (flat_map (fun '(_, l1, l2) => [l1; l2]) pack7_conflict_pairs ++ pack7_singletons)
     else true) pack7_uncovered = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pair_from_len2_hits_elem xs (a b bc : nat) :
  a <> b -> In a xs -> In b xs -> In bc xs -> length xs = 2 -> a = bc \/ b = bc.
Proof.
  intros Hne Ha Hb Hbc Hlen.
  destruct (Nat.eq_dec a bc) as [|H1]; [left; assumption|].
  destruct (Nat.eq_dec b bc) as [|H2]; [right; assumption|].
  exfalso.
  assert (Hnd : NoDup [bc; a; b]).
  { constructor; [simpl; intros [->|[->|[]]]; contradiction|].
    constructor; [simpl; intros [->|[]]; contradiction|constructor; [simpl; intros []|constructor]]. }
  assert (Hle : length [bc; a; b] <= length xs).
  { apply NoDup_incl_length; [exact Hnd|].
    intros z [<-|[<-|[<-|[]]]]; assumption. }
  simpl in Hle. lia.
Qed.

Lemma in_split_neq_2 {A} (x y : A) xs :
  In x xs -> In y xs -> x <> y ->
  exists a b c, xs = a ++ x :: b ++ y :: c \/ xs = a ++ y :: b ++ x :: c.
Proof.
  intros Hx Hy Hne. destruct (in_split _ _ Hx) as [a [b ->]].
  destruct (in_app_or _ _ _ Hy) as [Hy1|[Hy2|Hy3]].
  - destruct (in_split _ _ Hy1) as [u [v ->]]. exists u, v, b. right. rewrite <- app_assoc. reflexivity.
  - subst. contradiction.
  - destruct (in_split _ _ Hy3) as [u [v ->]]. exists a, u, v. left. reflexivity.
Qed.

Theorem pack7_max_residual_pairs_le_9 :
  forall (pairs : list (list cell * (cell * cell))),
    NoDup (map fst pairs) ->
    (forall l a b, In (l, (a, b)) pairs ->
      In l pack7_uncovered /\ In a l /\ In b l /\ a <> b /\ In a pack7_unused /\ In b pack7_unused) ->
    NoDup (flat_map (fun '(_, (a, b)) => [a; b]) pairs) ->
    length pairs <= 9.
Proof.
  intros pairs Hndl Hok Hndc.
  pose proof pack7_ge2_spec_b as Hspec. apply andb_true_iff in Hspec as [Hcp Hcov].
  rewrite forallb_forall in Hcp, Hcov.
  assert (Hpair_ge2 : forall l, In l (map fst pairs) ->
            In l (flat_map (fun '(_, l1, l2) => [l1; l2]) pack7_conflict_pairs ++ pack7_singletons)).
  { intros l Hl. apply in_map_iff in Hl as [[l' [a b]] [Heql Hp]]. simpl in Heql. subst l'.
    destruct (Hok l a b Hp) as (Hunc & Hal & Hbl & Hne & Hau & Hbu).
    set (s := filter (fun c => mem c pack7_unused) l).
    assert (Has : In a s) by (apply filter_In; split; [exact Hal|apply mem_spec, Hau]).
    assert (Hbs : In b s) by (apply filter_In; split; [exact Hbl|apply mem_spec, Hbu]).
    assert (Hlen2 : 2 <= length s).
    { destruct (in_split _ _ Has) as [s1 [s2 Hs]]. rewrite Hs in Hbs |- *.
      destruct (in_app_or _ _ _ Hbs) as [H1|[H2|H3]].
      - destruct s1; simpl in *; [contradiction|rewrite length_app; simpl; lia].
      - contradiction.
      - destruct s2; simpl in *; [contradiction|rewrite length_app; simpl; lia]. }
    specialize (Hcov l Hunc).
    replace (2 <=? length (filter (fun c => mem c pack7_unused) l)) with true in Hcov
      by (symmetry; apply Nat.leb_le, Hlen2).
    apply existsb_exists in Hcov as [x [Hx Heqx]].
    apply list_nat_eqb_eq in Heqx. subst x. exact Hx. }
  assert (Hcp_le1 : forall bc l1 l2, In (bc, l1, l2) pack7_conflict_pairs ->
            ~ (In l1 (map fst pairs) /\ In l2 (map fst pairs))).
  { intros bc l1 l2 Hcp_in [H1 H2].
    specialize (Hcp (bc, l1, l2) Hcp_in).
    apply andb_true_iff in Hcp as [Hcp Hlen2].
    apply andb_true_iff in Hcp as [Hcp Hbc2].
    apply andb_true_iff in Hcp as [Hcp Hlen1].
    apply andb_true_iff in Hcp as [Hneq Hbc1].
    apply negb_true_iff in Hneq.
    assert (Hl_neq : l1 <> l2) by (intro E; subst; rewrite (proj2 (list_nat_eqb_eq l2 l2) eq_refl) in Hneq; discriminate).
    apply in_map_iff in H1 as [[la [a1 b1]] [Ela Hpa]]. simpl in Ela. subst la.
    apply in_map_iff in H2 as [[lb [a2 b2]] [Elb Hpb]]. simpl in Elb. subst lb.
    destruct (Hok l1 a1 b1 Hpa) as (_ & Ha1l & Hb1l & Hne1 & Ha1u & Hb1u).
    destruct (Hok l2 a2 b2 Hpb) as (_ & Ha2l & Hb2l & Hne2 & Ha2u & Hb2u).
    apply Nat.eqb_eq in Hlen1. apply Nat.eqb_eq in Hlen2.
    apply mem_spec in Hbc1. apply mem_spec in Hbc2.
    assert (Hhit1 : a1 = bc \/ b1 = bc).
    { eapply pair_from_len2_hits_elem; [exact Hne1|..|exact Hbc1|exact Hlen1];
      apply filter_In; split; try assumption; apply mem_spec; assumption. }
    assert (Hhit2 : a2 = bc \/ b2 = bc).
    { eapply pair_from_len2_hits_elem; [exact Hne2|..|exact Hbc2|exact Hlen2];
      apply filter_In; split; try assumption; apply mem_spec; assumption. }
    assert (Hp_neq : (l1, (a1, b1)) <> (l2, (a2, b2))) by (intro E; inversion E; contradiction).
    assert (Hnd_two : forall (xs ys : list cell), NoDup (xs ++ ys) -> NoDup ys).
    { clear. intros xs ys. induction xs; simpl; auto. intros H. inversion H; auto. }
    destruct (in_split_neq_2 _ _ pairs Hpa Hpb Hp_neq) as [pa [pb [pc [Hpdec|Hpdec]]]];
    rewrite Hpdec in Hndc; repeat rewrite flat_map_app in Hndc; simpl in Hndc;
    apply Hnd_two in Hndc; rewrite flat_map_app in Hndc; simpl in Hndc.
    - assert (Hin1 : In bc [a1; b1]) by (simpl; destruct Hhit1; [left|right; left]; congruence).
      assert (Hin2 : In bc [a2; b2]) by (simpl; destruct Hhit2; [left|right; left]; congruence).
      destruct Hin1 as [<-|[<-|[]]]; destruct Hin2 as [E2|[E2|[]]];
        inversion Hndc as [|? ? Hna1 Hnt1]; subst.
      + apply Hna1. right. apply in_or_app; right; left; reflexivity.
      + apply Hna1. right. apply in_or_app; right; right; left; reflexivity.
      + inversion Hnt1 as [|? ? Hna2 _]; subst. apply Hna2. apply in_or_app; right; left; reflexivity.
      + inversion Hnt1 as [|? ? Hna2 _]; subst. apply Hna2. apply in_or_app; right; right; left; reflexivity.
    - assert (Hin1 : In bc [a1; b1]) by (simpl; destruct Hhit1; [left|right; left]; congruence).
      assert (Hin2 : In bc [a2; b2]) by (simpl; destruct Hhit2; [left|right; left]; congruence).
      destruct Hin2 as [<-|[<-|[]]]; destruct Hin1 as [E1|[E1|[]]];
        inversion Hndc as [|? ? Hna1 Hnt1]; subst.
      + apply Hna1. right. apply in_or_app; right; left; reflexivity.
      + apply Hna1. right. apply in_or_app; right; right; left; reflexivity.
      + inversion Hnt1 as [|? ? Hna2 _]; subst. apply Hna2. apply in_or_app; right; left; reflexivity.
      + inversion Hnt1 as [|? ? Hna2 _]; subst. apply Hna2. apply in_or_app; right; right; left; reflexivity. }
  rewrite <- (length_map fst pairs).
  set (ls := map fst pairs) in *.
  assert (Hsum_cp : forall (cp : list (cell * list cell * list cell)),
    (forall bc l1 l2, In (bc, l1, l2) cp -> ~ (In l1 ls /\ In l2 ls)) ->
    length (filter (fun l => existsb (fun '(_, l1, l2) => list_nat_eqb l l1 || list_nat_eqb l l2) cp) ls) <= length cp).
  { clear -Hndl. induction cp as [|[[bc l1] l2] t IH]; intros Hdisj; simpl.
    - clear. induction ls as [|x xs IHl]; simpl; [lia|exact IHl].
    - assert (Ht : length (filter (fun l => existsb (fun '(_, la, lb) => list_nat_eqb l la || list_nat_eqb l lb) t) ls) <= length t)
        by (apply IH; intros bc0 la lb Hin; apply (Hdisj bc0 la lb); right; exact Hin).
      assert (Hpair1 : length (filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) ls) <= 1).
      { assert (Hdisj_ab : ~ (In l1 ls /\ In l2 ls)) by (apply (Hdisj bc l1 l2); left; reflexivity).
        pose proof (NoDup_filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) Hndl) as Hndf.
        destruct (filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) ls) as [|a [|b tl]] eqn:Ef; [simpl; lia|simpl; lia|].
        exfalso.
        assert (Ha : In a (filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) ls)) by (rewrite Ef; left; reflexivity).
        assert (Hb : In b (filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) ls)) by (rewrite Ef; right; left; reflexivity).
        apply filter_In in Ha as [Hals Fa]. apply orb_true_iff in Fa as [Ea|Ea]; apply list_nat_eqb_eq in Ea; subst a;
        apply filter_In in Hb as [Hbls Fb]; apply orb_true_iff in Fb as [Eb|Eb]; apply list_nat_eqb_eq in Eb; subst b.
        - inversion Hndf; subst. apply H1. left. reflexivity.
        - apply Hdisj_ab. split; assumption.
        - apply Hdisj_ab. split; assumption.
        - inversion Hndf; subst. apply H1. left. reflexivity. }
      assert (Hor_le : forall (f g : list cell -> bool) xs,
        length (filter (fun x => f x || g x) xs) <= length (filter f xs) + length (filter g xs)).
      { clear. intros f g xs. induction xs as [|x xs IHx]; simpl; [lia|].
        destruct (f x), (g x); simpl in *; lia. }
      pose proof (Hor_le (fun l => list_nat_eqb l l1 || list_nat_eqb l l2)
                         (fun l => existsb (fun '(_, la, lb) => list_nat_eqb l la || list_nat_eqb l lb) t) ls) as Hsplit.
      assert (Hrhs : length (filter (fun l => list_nat_eqb l l1 || list_nat_eqb l l2) ls) +
        length (filter (fun l => existsb (fun '(_, la, lb) => list_nat_eqb l la || list_nat_eqb l lb) t) ls) <= S (length t)) by lia.
      exact (Nat.le_trans _ _ _ Hsplit Hrhs). }
  assert (Hpart_ls : length ls <=
    length (filter (fun l => existsb (fun '(_, l1, l2) => list_nat_eqb l l1 || list_nat_eqb l l2) pack7_conflict_pairs) ls) +
    length (filter (fun l => existsb (fun s => list_nat_eqb l s) pack7_singletons) ls)).
  { assert (Hgen : forall (P1 P2 : list cell -> bool) (ys : list (list cell)),
      (forall x, In x ys -> P1 x = true \/ P2 x = true) ->
      length ys <= length (filter P1 ys) + length (filter P2 ys)).
    { clear. intros P1 P2 ys. induction ys as [|x xs IH]; intros Hsub; simpl; [lia|].
      assert (IH' : length xs <= length (filter P1 xs) + length (filter P2 xs))
        by (apply IH; intros y Hy; apply Hsub; right; exact Hy).
      destruct (Hsub x (or_introl eq_refl)) as [H1|H2].
      - rewrite H1. destruct (P2 x); simpl; lia.
      - rewrite H2. destruct (P1 x); simpl; lia. }
    apply Hgen. intros x Hx.
    pose proof (Hpair_ge2 x Hx) as Hinx. apply in_app_or in Hinx as [Hinx|Hinx].
    - left. apply existsb_exists. apply in_flat_map in Hinx as [[[bc l1] l2] [Hcp' Hin12]].
      exists (bc, l1, l2). split; [exact Hcp'|].
      simpl in Hin12. destruct Hin12 as [<-|[<-|[]]]; rewrite (proj2 (list_nat_eqb_eq _ _) eq_refl); [|rewrite orb_true_r]; reflexivity.
    - right. apply existsb_exists. exists x. split; [exact Hinx|apply list_nat_eqb_eq; reflexivity]. }
  assert (Hsing_le5 : length (filter (fun l => existsb (fun s => list_nat_eqb l s) pack7_singletons) ls) <= length pack7_singletons).
  { apply NoDup_incl_length; [apply NoDup_filter, Hndl|].
    intros x Hx. apply filter_In in Hx as [_ Hx].
    apply existsb_exists in Hx as [s [Hs Heq]]. apply list_nat_eqb_eq in Heq. subst. exact Hs. }
  specialize (Hsum_cp pack7_conflict_pairs Hcp_le1).
  change (length pack7_conflict_pairs) with 4 in Hsum_cp.
  change (length pack7_singletons) with 5 in Hsing_le5.
  lia.
Qed.

Definition z_of (c : cell) : nat := c / 25.

Definition w_col0 : WhiteStrategy :=
  fun st => nth (length (white_stones st)) [0; 25; 50; 75; 100] 0.

Theorem pack7_uncoordinated_z_slice_loses : forall b : BlackStrategy,
  (forall st x rest, history st = x :: rest -> z_of (effective_move st (b st)) = z_of x) ->
  outcome (play w_col0 b) = WhiteWins.
Proof.
  intros b Hz. unfold play.
  assert (Hshort_no_win : forall stones, length stones <= 4 -> has_win stones = false).
  { intros stones Hlen. destruct (has_win stones) eqn:Hw; [|reflexivity]. exfalso.
    unfold has_win in Hw. apply existsb_exists in Hw as [l [Hl Hline]].
    assert (H5 : 5 <= length stones).
    { rewrite <- (line_length l Hl). apply NoDup_incl_length; [apply line_nodup, Hl|].
      intros c Hc. unfold has_line in Hline. apply forallb_forall with (x := c) in Hline; [apply mem_spec, Hline|exact Hc]. }
    lia. }
  assert (Hrun : forall d steps k st,
    d = 4 - k ->
    steps + length (history st) = 125 ->
    valid_state st ->
    length (history st) = 2 * k ->
    length (white_stones st) = k ->
    length (black_stones st) = k ->
    k <= 4 ->
    (forall i, i < k -> In (25 * i) (white_stones st)) ->
    (forall m, k <= m -> m < 5 -> occupied st (25 * m) = false) ->
    outcome (step_game steps true st w_col0 b) = WhiteWins).
  { intro d. induction d as [|d IH]; intros steps k st Hd Hsum Hval Hhist Hwl Hbl Hk4 Hwi Hocc.
    - assert (Hk : k = 4) by lia. rewrite Hk in Hwl, Hhist, Hbl, Hwi, Hocc.
      destruct steps as [|steps]; [lia|].
      rewrite step_game_equation. cbn zeta.
      set (st1 := move_state true st (w_col0 st)).
      assert (Hw_req : w_col0 st = 100) by (unfold w_col0; rewrite Hwl; reflexivity).
      assert (Hleg : is_legal_move st 100 = true).
      { unfold is_legal_move. apply andb_true_iff. split; [reflexivity|].
        change 100 with (25 * 4). rewrite (Hocc 4 ltac:(lia) ltac:(lia)). reflexivity. }
      assert (Heff : effective_move st (w_col0 st) = 100) by (rewrite Hw_req; apply effective_legal, Hleg).
      assert (Hwin : has_win (white_stones st1) = true).
      { unfold has_win. apply existsb_exists. exists [0; 25; 50; 75; 100]. split.
        - vm_compute. repeat (try (left; reflexivity); right).
        - unfold has_line, st1, move_state. cbn [white_stones]. rewrite Heff.
          apply forallb_forall. intros c [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply existsb_exists.
          + exists 0; split; [change 0 with (25 * 0); right; apply Hwi; lia|reflexivity].
          + exists 25; split; [change 25 with (25 * 1); right; apply Hwi; lia|reflexivity].
          + exists 50; split; [change 50 with (25 * 2); right; apply Hwi; lia|reflexivity].
          + exists 75; split; [change 75 with (25 * 3); right; apply Hwi; lia|reflexivity].
          + exists 100; split; [left; reflexivity|reflexivity]. }
      unfold move_result. rewrite Hwin. reflexivity.
    - assert (Hk_lt : k < 4) by lia.
      destruct steps as [|steps]; [lia|].
      rewrite step_game_equation. cbn zeta.
      assert (Hw_req : w_col0 st = 25 * k).
      { unfold w_col0. rewrite Hwl. destruct k as [|[|[|[|k']]]]; [reflexivity|reflexivity|reflexivity|reflexivity|lia]. }
      assert (Hleg : is_legal_move st (25 * k) = true).
      { unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt; lia|rewrite (Hocc k ltac:(lia) ltac:(lia)); reflexivity]. }
      assert (Heff : effective_move st (w_col0 st) = 25 * k) by (rewrite Hw_req; apply effective_legal, Hleg).
      set (st1 := move_state true st (w_col0 st)).
      assert (Hval1 : valid_state st1) by (apply move_preserves_validity; [exact Hval|lia]).
      assert (Hlen1 : length (history st1) = S (2 * k)) by (unfold st1; rewrite move_state_history; lia).
      unfold move_result at 1. destruct (has_win (white_stones st1)) eqn:Hw1; [reflexivity|].
      replace (length (history st1) =? 125) with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct steps as [|steps]; [lia|].
      rewrite step_game_equation. cbn zeta. change (negb true) with false.
      set (st2 := move_state false st1 (b st1)).
      assert (Hlen2 : length (history st2) = 2 * S k) by (unfold st2; rewrite move_state_history; lia).
      assert (Hval2 : valid_state st2) by (apply move_preserves_validity; [exact Hval1|lia]).
      assert (Hb_nowin : has_win (black_stones st2) = false).
      { apply Hshort_no_win. unfold st2, st1, move_state. simpl. lia. }
      unfold move_result. cbn iota. rewrite Hb_nowin.
      replace (length (history st2) =? 125) with false by (symmetry; apply Nat.eqb_neq; lia).
      change (negb false) with true.
      assert (Hz_y : z_of (effective_move st1 (b st1)) = k).
      { rewrite (Hz st1 (25 * k) (history st) ltac:(unfold st1, move_state; simpl; rewrite Heff; reflexivity)).
        unfold z_of. rewrite Nat.mul_comm, Nat.div_mul by lia. reflexivity. }
      apply (IH steps (S k) st2 ltac:(lia)); try assumption; try lia.
      + unfold st2, st1, move_state. simpl. lia.
      + unfold st2, st1, move_state. simpl. lia.
      + intros i Hi. unfold st2, st1, move_state. simpl. rewrite Heff.
        destruct (Nat.eq_dec i k) as [->|Hne]; [left; reflexivity|right; apply Hwi; lia].
      + intros m Hm1 Hm2.
        assert (Hm_ne : 25 * m <> effective_move st1 (b st1)).
        { intros E. apply (f_equal z_of) in E. rewrite Hz_y in E.
          unfold z_of in E. rewrite Nat.mul_comm, Nat.div_mul in E by lia. lia. }
        unfold st2, st1, occupied, move_state. cbn [white_stones black_stones].
        rewrite Heff. pose proof (Hocc m ltac:(lia) Hm2) as H0. unfold occupied in H0.
        apply orb_false_iff in H0 as [Hw0 Hb0].
        apply orb_false_iff. split; apply Bool.not_true_iff_false; intros Hin; apply mem_spec in Hin.
        { destruct Hin as [E|Hin]; [lia | apply (proj2 (mem_spec _ _)) in Hin; unfold mem in Hin; rewrite Hw0 in Hin; discriminate]. }
        { destruct Hin as [E|Hin]; [apply Hm_ne; unfold st1, move_state; simpl; rewrite Heff; symmetry; exact E | apply (proj2 (mem_spec _ _)) in Hin; unfold mem in Hin; rewrite Hb0 in Hin; discriminate]. } }
  apply (Hrun 4 125 0 initial_state eq_refl); [reflexivity|apply initial_state_valid|reflexivity|reflexivity|reflexivity|lia|intros i Hi; lia|intros; reflexivity].
Qed.

(** ** 3. Phi < 1.0 Soundness Counterexample (`HandOff.md` Lines 81 & 148) *)

Definition cex54_moves : list cell := [
  1; 4; 5; 6; 10; 14; 13; 17; 15; 23; 24; 27; 25; 30; 32;
  38; 34; 41; 48; 49; 50; 53; 54; 57; 59; 60; 65; 61; 68; 62;
  73; 69; 75; 72; 83; 76; 91; 84; 96; 87; 98; 93; 102; 95; 106;
  104; 110; 108; 113; 112; 120; 115; 124; 121
].

Definition st_cex54 : GameState := replay_moves initial_state true cex54_moves.
Definition st_cex54_nf : GameState := Eval vm_compute in st_cex54.

Lemma st_cex54_eq : st_cex54 = st_cex54_nf.
Proof. vm_compute. reflexivity. Qed.

Lemma cex54_valid : valid_state st_cex54 /\ length (history st_cex54) = 54.
Proof. apply replay_initial_valid; vm_compute; try reflexivity; lia. Qed.

Lemma cex54_props :
  quiet st_cex54 /\
  phi (fun _ => 0) (fun _ => 0) st_cex54 0 = 16 /\
  occupied st_cex54 0 = false /\
  occupied st_cex54 20 = false /\
  occupied st_cex54 100 = false /\
  forallb (fun y => negb (has_win (y :: black_stones st_cex54_nf))) all_cells = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition w_fork54 : WhiteStrategy :=
  fun st =>
    if negb (occupied st 0) then 0
    else if negb (occupied st 20) then 20
    else 100.

Lemma mem_cons_inv x c xs : mem x (c :: xs) = true -> mem x xs = false -> x = c.
Proof.
  unfold mem; simpl; destruct (Nat.eqb x c) eqn:E;
    [intros _ _; apply Nat.eqb_eq, E | intros H1 H2; simpl in H1; rewrite H1 in H2; discriminate].
Qed.

Theorem phi_lt_32_unsound : forall b : BlackStrategy,
  outcome (step_game 71 true st_cex54 w_fork54 b) = WhiteWins.
Proof.
  intros b.
  destruct cex54_props as (_ & _ & H0free & _ & _ & Hnob4).
  pose proof cex54_valid as [Hv0 Hl0].
  rewrite st_cex54_eq in H0free, Hv0, Hl0 |- *.
  rewrite step_game_equation. cbn zeta.
  assert (Hw1 : w_fork54 st_cex54_nf = 0) by (unfold w_fork54; rewrite H0free; reflexivity).
  assert (Hleg1 : is_legal_move st_cex54_nf 0 = true)
    by (unfold is_legal_move; rewrite H0free; reflexivity).
  assert (Heff1 : effective_move st_cex54_nf (w_fork54 st_cex54_nf) = 0)
    by (rewrite Hw1; apply effective_legal, Hleg1).
  set (st1 := move_state true st_cex54_nf (w_fork54 st_cex54_nf)).
  assert (Hw_st1 : white_stones st1 = 0 :: white_stones st_cex54_nf)
    by (unfold st1, move_state; cbn [white_stones]; rewrite Heff1; reflexivity).
  assert (Hb_st1 : black_stones st1 = black_stones st_cex54_nf)
    by (unfold st1, move_state; cbn [black_stones]; reflexivity).
  assert (Hval1 : valid_state st1)
    by (apply move_preserves_validity; [exact Hv0|lia]).
  assert (Hlen1 : length (history st1) = 55)
    by (unfold st1; rewrite move_state_history; lia).
  assert (Hnw1 : has_win (white_stones st1) = false)
    by (rewrite Hw_st1; vm_compute; reflexivity).
  unfold move_result at 1. rewrite Hnw1.
  replace (length (history st1) =? 125) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite step_game_equation. cbn zeta. change (negb true) with false.
  set (y := effective_move st1 (b st1)).
  assert (Hleg_y : is_legal_move st1 y = true) by (apply effective_move_is_legal; [exact Hval1|lia]).
  assert (Hy125 : y < 125)
    by (unfold is_legal_move in Hleg_y; apply andb_true_iff in Hleg_y as [Hy125 _]; apply Nat.ltb_lt; exact Hy125).
  set (st2 := move_state false st1 (b st1)).
  assert (Hw_st2 : white_stones st2 = 0 :: white_stones st_cex54_nf)
    by (unfold st2, move_state; cbn [white_stones]; exact Hw_st1).
  assert (Hb_st2 : black_stones st2 = y :: black_stones st_cex54_nf)
    by (unfold st2, move_state; cbn [black_stones]; fold y; rewrite Hb_st1; reflexivity).
  assert (Hbw2 : has_win (black_stones st2) = false).
  { rewrite Hb_st2.
    rewrite forallb_forall in Hnob4.
    specialize (Hnob4 y (proj2 (all_cells_spec y) Hy125)). apply negb_true_iff, Hnob4. }
  assert (Hlen2 : length (history st2) = 56)
    by (unfold st2; rewrite move_state_history; lia).
  unfold move_result. cbn iota. rewrite Hbw2.
  replace (length (history st2) =? 125) with false by (symmetry; apply Nat.eqb_neq; lia).
  change (negb false) with true.
  rewrite step_game_equation. cbn zeta.
  assert (Hocc0_2 : occupied st2 0 = true)
    by (unfold occupied; rewrite Hw_st2; reflexivity).
  assert (Hw_eq0 : w_fork54 st2 = if negb (occupied st2 20) then 20 else 100)
    by (unfold w_fork54; rewrite Hocc0_2; reflexivity).
  set (st3 := move_state true st2 (w_fork54 st2)).
  assert (Hw_st3 : white_stones st3 = effective_move st2 (w_fork54 st2) :: 0 :: white_stones st_cex54_nf)
    by (unfold st3, move_state; cbn [white_stones]; rewrite Hw_st2; reflexivity).
  assert (Hocc20_1 : occupied st1 20 = false)
    by (unfold occupied; rewrite Hw_st1, Hb_st1; vm_compute; reflexivity).
  assert (Hocc100_1 : occupied st1 100 = false)
    by (unfold occupied; rewrite Hw_st1, Hb_st1; vm_compute; reflexivity).
  assert (Hwin3 : has_win (white_stones st3) = true).
  { destruct (occupied st2 20) eqn:E20.
    - assert (Hw_100 : w_fork54 st2 = 100) by exact Hw_eq0.
      assert (Hy_is_20 : y = 20).
      { unfold occupied in E20, Hocc20_1.
        rewrite Hw_st2, Hb_st2 in E20. rewrite Hw_st1, Hb_st1 in Hocc20_1.
        apply orb_true_iff in E20 as [Ew|Eb]; apply orb_false_iff in Hocc20_1 as [Hw Hb].
        - rewrite Ew in Hw. discriminate.
        - symmetry. exact (mem_cons_inv 20 y (black_stones st_cex54_nf) Eb Hb). }
      assert (Hocc100_2 : occupied st2 100 = false)
        by (unfold occupied; rewrite Hw_st2, Hb_st2, Hy_is_20; vm_compute; reflexivity).
      assert (Hleg3 : is_legal_move st2 100 = true) by (unfold is_legal_move; rewrite Hocc100_2; reflexivity).
      assert (Heff3 : effective_move st2 (w_fork54 st2) = 100) by (rewrite Hw_100; apply effective_legal, Hleg3).
      rewrite Hw_st3, Heff3. vm_compute. reflexivity.
    - assert (Hw_20 : w_fork54 st2 = 20) by exact Hw_eq0.
      assert (Hleg3 : is_legal_move st2 20 = true) by (unfold is_legal_move; rewrite E20; reflexivity).
      assert (Heff3 : effective_move st2 (w_fork54 st2) = 20) by (rewrite Hw_20; apply effective_legal, Hleg3).
      rewrite Hw_st3, Heff3. vm_compute. reflexivity. }
  unfold move_result. rewrite Hwin3. reflexivity.
Qed.

(** ** 4. Real Midgame Strict Separation Witnesses (`res032 id=0 ply=26` & `res029 id=15 ply=24`) *)

(* Witness 1: research-032/mb_equal.jsonl id=0 at ply=26 *)
Definition w26_moves : list cell := [
  0; 20; 62; 31; 24; 43; 120; 104; 4; 33; 100; 12; 52; 76; 72;
  67; 48; 96; 124; 50; 122; 123; 2; 3; 102; 32
].

Definition w26_st : GameState := replay_moves initial_state true w26_moves.

Definition w26_reg_tbl : list nat := [
  999; 21; 999; 999; 999; 36; 21; 10; 10; 22; 0; 0; 999; 0; 0;
  38; 39; 11; 11; 22; 999; 48; 49; 999; 999; 23; 12; 35; 12; 24;
  47; 999; 999; 999; 37; 0; 0; 999; 0; 0; 23; 39; 49; 999; 40;
  13; 13; 41; 999; 24; 999; 25; 999; 26; 27; 36; 14; 14; 43; 37;
  47; 15; 999; 15; 50; 38; 25; 999; 26; 27; 43; 16; 999; 16; 42;
  44; 999; 35; 30; 31; 17; 44; 17; 45; 31; 28; 0; 29; 0; 0;
  28; 18; 29; 18; 50; 45; 999; 41; 30; 42; 999; 48; 999; 999; 999;
  32; 46; 34; 19; 19; 0; 33; 46; 0; 0; 32; 20; 34; 20; 40;
  999; 33; 999; 999; 999
].

Definition w26_asg_buckets : list (list (nat * nat)) := [
  [(1, 998); (5, 998); (25, 998); (6, 998); (26, 998); (30, 47); (31, 998)];
  [(6, 21); (26, 998); (31, 998)];
  [(7, 998); (27, 35); (32, 998)];
  [(8, 998); (28, 998); (33, 998)];
  [(9, 22); (29, 998); (8, 998); (28, 998); (34, 50); (33, 998)];
  [(6, 10); (30, 36); (31, 998)];
  [(31, 998)];
  [(32, 998)];
  [(33, 998)];
  [(34, 37); (33, 998)];
  [(11, 998); (35, 0); (36, 0)];
  [(36, 0)];
  [(37, 998)];
  [(38, 0)];
  [(39, 0); (38, 0)];
  [(16, 11); (40, 38); (41, 998)];
  [(41, 39)];
  [(42, 998)];
  [(43, 998)];
  [(44, 40); (43, 998)];
  [(21, 998); (45, 998); (46, 998); (40, 998); (41, 998)];
  [(46, 998); (41, 48)];
  [(47, 41); (42, 49)];
  [(48, 998); (43, 998)];
  [(49, 42); (48, 998); (44, 998); (43, 998)];
  [(26, 12); (30, 23); (31, 998)];
  [(31, 998)];
  [(32, 998)];
  [(33, 998)];
  [(34, 24); (33, 998)];
  [(31, 998)];
  [];
  [];
  [];
  [];
  [(36, 0)];
  [];
  [];
  [];
  [];
  [(41, 998)];
  [];
  [];
  [];
  [];
  [(46, 13)];
  [];
  [];
  [];
  [];
  [(51, 998); (55, 998); (56, 998)];
  [(56, 25)];
  [(57, 998)];
  [(58, 26)];
  [(59, 27); (58, 43)];
  [(56, 14)];
  [];
  [];
  [];
  [];
  [(61, 15)];
  [];
  [];
  [];
  [];
  [(66, 998)];
  [];
  [];
  [];
  [];
  [(71, 16)];
  [];
  [];
  [];
  [];
  [(76, 998); (80, 28); (81, 44)];
  [(81, 998)];
  [(82, 29)];
  [(83, 30)];
  [(84, 31); (83, 45)];
  [(81, 17)];
  [];
  [];
  [];
  [];
  [(86, 0)];
  [];
  [];
  [];
  [];
  [(91, 18)];
  [];
  [];
  [];
  [];
  [(96, 998)];
  [];
  [];
  [];
  [];
  [(101, 998); (105, 32); (106, 46)];
  [(106, 33)];
  [(107, 34)];
  [(108, 998)];
  [(109, 998); (108, 998)];
  [(106, 19)];
  [];
  [];
  [];
  [];
  [(111, 0)];
  [];
  [];
  [];
  [];
  [(116, 20)];
  [];
  [];
  [];
  [];
  [(121, 998)];
  [];
  [];
  [];
  []
].

Definition w26_reg : cell -> nat := table_reg w26_reg_tbl 999.
Definition w26_asg : list cell -> nat := bucket_asg w26_asg_buckets 998.

Definition w26_g0 : EmbeddedGadget :=
  mk_emb_gadget 0
    [110; 113; 114; 86; 88; 89; 35; 36; 38; 39; 10; 11; 13; 14]
    gadget_Slice14
    [
    ([35; 36; 37; 38; 39], 2);
    ([85; 86; 87; 88; 89], 1);
    ([110; 111; 112; 113; 114], 0);
    ([10; 35; 60; 85; 110], 4);
    ([11; 36; 61; 86; 111], 5);
    ([13; 38; 63; 88; 113], 6);
    ([14; 39; 64; 89; 114], 7);
    ([10; 36; 62; 88; 114], 9);
    ([14; 38; 62; 86; 110], 8)
  ].

Definition w26_gs : list EmbeddedGadget := [w26_g0].

Lemma w26_valid : valid_state w26_st /\ length (history w26_st) = 26.
Proof. apply replay_initial_valid; vm_compute; try reflexivity; lia. Qed.

Theorem w26_pairing_impossible :
  length (alive_lines_of w26_st) = 50 /\
  length (empty_cells_of w26_st) = 99 /\
  (ValidPairing (alive_lines_of w26_st) (empty_cells_of w26_st) -> False).
Proof.
  assert (Hcnt : length (alive_lines_of w26_st) = 50 /\ length (empty_cells_of w26_st) = 99)
    by (vm_compute; split; reflexivity).
  destruct Hcnt as [Hc1 Hc2].
  split; [exact Hc1 | split; [exact Hc2 | ]].
  intros Hvp. apply (no_pairing_when_deficit (alive_lines_of w26_st) (empty_cells_of w26_st)).
  - apply NoDup_filter, all_lines_nodup.
  - lia.
  - exact Hvp.
Qed.

Theorem w26_cert_ok : hybrid_certificateb w26_reg w26_asg w26_gs w26_st = true.
Proof. vm_compute. reflexivity. Qed.

Theorem res032_id0_ply26_nonloss : forall w,
  outcome (step_game 99 true w26_st w (hybrid_policy w26_reg w26_asg w26_gs)) <> WhiteWins.
Proof.
  intros w. destruct w26_valid as [Hv Hl].
  apply hybrid_certificate_nonloss; [exact Hv|lia|exact w26_cert_ok].
Qed.

(* Witness 2: research-029/games_cert.jsonl id=15 at ply=24 *)
Definition w24_moves : list cell := [
  0; 20; 62; 124; 72; 52; 4; 120; 2; 24; 1; 3; 22; 122; 121;
  31; 70; 74; 21; 58; 49; 33; 46; 83
].

Definition w24_st : GameState := replay_moves initial_state true w24_moves.

Definition w24_reg_tbl : list nat := [
  999; 999; 999; 999; 999; 35; 19; 36; 10; 10; 1; 19; 20; 1; 1;
  0; 0; 20; 0; 0; 999; 999; 999; 41; 999; 11; 33; 22; 11; 23;
  35; 999; 22; 999; 23; 21; 1; 38; 1; 1; 0; 0; 44; 0; 0;
  21; 999; 12; 12; 999; 32; 33; 999; 999; 34; 24; 25; 36; 999; 37;
  13; 43; 999; 999; 13; 24; 25; 39; 14; 14; 999; 40; 999; 41; 999;
  42; 27; 15; 15; 29; 26; 27; 44; 999; 29; 1; 1; 38; 1; 1;
  26; 0; 28; 0; 0; 16; 40; 28; 16; 42; 32; 43; 17; 17; 34;
  18; 30; 18; 31; 37; 1; 1; 999; 1; 1; 0; 30; 39; 0; 0;
  999; 999; 999; 31; 999
].

Definition w24_asg_buckets : list (list (nat * nat)) := [
  [(1, 998); (5, 998); (25, 32); (6, 998); (26, 998); (30, 998); (31, 998)];
  [(6, 19); (26, 33); (31, 998)];
  [(7, 20); (27, 998); (32, 998)];
  [(8, 998); (28, 998); (33, 998)];
  [(9, 998); (29, 34); (8, 998); (28, 998); (34, 998); (33, 998)];
  [(6, 10); (30, 35); (31, 998)];
  [(31, 998)];
  [(32, 36)];
  [(33, 998)];
  [(34, 37); (33, 998)];
  [(11, 1); (35, 1); (36, 1)];
  [(36, 1)];
  [(37, 38)];
  [(38, 1)];
  [(39, 1); (38, 1)];
  [(16, 0); (40, 0); (41, 0)];
  [(41, 0)];
  [(42, 39)];
  [(43, 0)];
  [(44, 0); (43, 0)];
  [(21, 998); (45, 998); (46, 998); (40, 998); (41, 998)];
  [(46, 40); (41, 43)];
  [(47, 998); (42, 44)];
  [(48, 41); (43, 998)];
  [(49, 998); (48, 998); (44, 998); (43, 998)];
  [(26, 11); (30, 21); (31, 998)];
  [(31, 998)];
  [(32, 22)];
  [(33, 998)];
  [(34, 23); (33, 998)];
  [(31, 998)];
  [];
  [];
  [];
  [];
  [(36, 1)];
  [];
  [];
  [];
  [];
  [(41, 0)];
  [];
  [];
  [];
  [];
  [(46, 12)];
  [];
  [];
  [];
  [];
  [(51, 998); (55, 24); (56, 998)];
  [(56, 25)];
  [(57, 998)];
  [(58, 998)];
  [(59, 998); (58, 998)];
  [(56, 998)];
  [];
  [];
  [];
  [];
  [(61, 13)];
  [];
  [];
  [];
  [];
  [(66, 14)];
  [];
  [];
  [];
  [];
  [(71, 998)];
  [];
  [];
  [];
  [];
  [(76, 15); (80, 26); (81, 42)];
  [(81, 27)];
  [(82, 28)];
  [(83, 998)];
  [(84, 29); (83, 998)];
  [(81, 998)];
  [];
  [];
  [];
  [];
  [(86, 1)];
  [];
  [];
  [];
  [];
  [(91, 0)];
  [];
  [];
  [];
  [];
  [(96, 16)];
  [];
  [];
  [];
  [];
  [(101, 17); (105, 998); (106, 998)];
  [(106, 30)];
  [(107, 998)];
  [(108, 31)];
  [(109, 998); (108, 998)];
  [(106, 18)];
  [];
  [];
  [];
  [];
  [(111, 1)];
  [];
  [];
  [];
  [];
  [(116, 0)];
  [];
  [];
  [];
  [];
  [(121, 998)];
  [];
  [];
  [];
  []
].

Definition w24_reg : cell -> nat := table_reg w24_reg_tbl 999.
Definition w24_asg : list cell -> nat := bucket_asg w24_asg_buckets 998.

Definition w24_g0 : EmbeddedGadget :=
  mk_emb_gadget 0
    [91; 94; 93; 115; 119; 118; 16; 15; 19; 18; 41; 40; 44; 43]
    gadget_Slice14
    [
    ([15; 16; 17; 18; 19], 2);
    ([40; 41; 42; 43; 44], 3);
    ([90; 91; 92; 93; 94], 0);
    ([115; 116; 117; 118; 119], 1);
    ([15; 40; 65; 90; 115], 5);
    ([16; 41; 66; 91; 116], 4);
    ([18; 43; 68; 93; 118], 7);
    ([19; 44; 69; 94; 119], 6);
    ([15; 41; 67; 93; 119], 9);
    ([19; 43; 67; 91; 115], 8)
  ].

Definition w24_g1 : EmbeddedGadget :=
  mk_emb_gadget 1
    [10; 13; 14; 36; 38; 39; 85; 86; 88; 89; 110; 111; 113; 114]
    gadget_Slice14
    [
    ([10; 11; 12; 13; 14], 0);
    ([35; 36; 37; 38; 39], 1);
    ([85; 86; 87; 88; 89], 2);
    ([110; 111; 112; 113; 114], 3);
    ([10; 35; 60; 85; 110], 4);
    ([11; 36; 61; 86; 111], 5);
    ([13; 38; 63; 88; 113], 6);
    ([14; 39; 64; 89; 114], 7);
    ([10; 36; 62; 88; 114], 8);
    ([14; 38; 62; 86; 110], 9)
  ].

Definition w24_gs : list EmbeddedGadget := [w24_g0; w24_g1].

Lemma w24_valid : valid_state w24_st /\ length (history w24_st) = 24.
Proof. apply replay_initial_valid; vm_compute; try reflexivity; lia. Qed.

Theorem w24_pairing_impossible :
  length (alive_lines_of w24_st) = 55 /\
  length (empty_cells_of w24_st) = 101 /\
  (ValidPairing (alive_lines_of w24_st) (empty_cells_of w24_st) -> False).
Proof.
  assert (Hcnt : length (alive_lines_of w24_st) = 55 /\ length (empty_cells_of w24_st) = 101)
    by (vm_compute; split; reflexivity).
  destruct Hcnt as [Hc1 Hc2].
  split; [exact Hc1 | split; [exact Hc2 | ]].
  intros Hvp. apply (no_pairing_when_deficit (alive_lines_of w24_st) (empty_cells_of w24_st)).
  - apply NoDup_filter, all_lines_nodup.
  - lia.
  - exact Hvp.
Qed.

Theorem w24_cert_ok : hybrid_certificateb w24_reg w24_asg w24_gs w24_st = true.
Proof. vm_compute. reflexivity. Qed.

Theorem res029_id15_ply24_nonloss : forall w,
  outcome (step_game 101 true w24_st w (hybrid_policy w24_reg w24_asg w24_gs)) <> WhiteWins.
Proof.
  intros w. destruct w24_valid as [Hv Hl].
  apply hybrid_certificate_nonloss; [exact Hv|lia|exact w24_cert_ok].
Qed.

Print Assumptions pack7_max_residual_pairs_le_9.
Print Assumptions pack7_uncoordinated_z_slice_loses.
Print Assumptions phi_lt_32_unsound.
Print Assumptions res032_id0_ply26_nonloss.
Print Assumptions res029_id15_ply24_nonloss.
