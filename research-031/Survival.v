(** Research 031: a fork-aware Black policy delays any White win to ply 17.

    Policy [cross_policy]: block a White completion cell if one exists;
    otherwise occupy a White *fork cell* (a cell where a White stone would
    create two distinct completion cells); otherwise request cell 0.

    Argument (no game-tree enumeration):
    - White's first fork appears only through a fork cell left open by Black:
      both threatened lines contain White's last stone.
    - A fork cell needs two lines through it with three White stones each,
      i.e. six White stones. With at most six White stones those six are all
      of White's stones, so there is no second fork cell and no threat beside
      it (two lines share at most one cell). One Black move removes every
      danger in rounds 1..6.
    - Hence there is no fork after White's 7th move, its completion is unique
      and blocked, and White cannot win on move 8. A White win needs at
      least 17 plies (the previous bound, research 019, was 15). *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Geometry Minimax RulesFacts SafePairing Stealing Tactics.
Import ListNotations.

(** * 1. Line facts *)

Lemma without_In : forall x c l, In x (without c l) <-> In x l /\ x <> c.
Proof.
  intros x c l. unfold without. rewrite filter_In, negb_true_iff, Nat.eqb_neq.
  split; intros [H1 H2]; split; try exact H1; intro E; apply H2; congruence.
Qed.

Lemma two_common_cells : forall a b x y,
  In a all_lines -> In b all_lines -> a <> b ->
  In x a -> In x b -> In y a -> In y b -> x = y.
Proof.
  intros a b x y Ha Hb Hab Hxa Hxb Hya Hyb.
  destruct (Nat.eq_dec x y) as [E|Hne]; [exact E|exfalso].
  pose proof (winning_lines_linear a b Ha Hb Hab) as Hlin.
  assert (Hincl : incl [x; y] (intersection a b)).
  { intros z [Hz|[Hz|[]]]; subst z; unfold intersection; apply filter_In;
      split; try assumption; apply member_spec; assumption. }
  assert (Hnd2 : NoDup [x; y]).
  { constructor; [intros [H|[]]; congruence|constructor; [intros []|constructor]]. }
  pose proof (NoDup_incl_length Hnd2 Hincl) as Hl. cbn in Hl. lia.
Qed.

Lemma threat_wins : forall stones l d, four_threat stones l d -> has_win (d :: stones) = true.
Proof.
  intros stones l d [Hl [Hd [_ Hall]]]. unfold has_win. apply existsb_exists.
  exists l. split; [exact Hl|]. unfold has_line. apply forallb_forall. intros x Hx.
  apply member_spec. destruct (Nat.eq_dec x d) as [E|Hne];
    [left; congruence|right; apply Hall; assumption].
Qed.

(** A completion created by adding [c] lies on a line through [c]. *)
Lemma fork_line : forall W c d,
  ~ In c W -> ~ In d W -> d <> c ->
  has_win (c :: W) = false -> has_win (d :: W) = false -> has_win (d :: c :: W) = true ->
  exists L, In L all_lines /\ In c L /\ In d L /\
    (forall x, In x L -> x <> c -> x <> d -> In x W).
Proof.
  intros W c d HcW HdW Hdc Hc Hd Hwin.
  assert (Hnot : ~ In d (c :: W)) by (intros [H|H]; [congruence|contradiction]).
  destruct (added_win_gives_threat (c :: W) d Hc Hnot Hwin) as [L HL].
  destruct HL as [Hl [HdL [_ Hall]]].
  destruct (in_dec Nat.eq_dec c L) as [HcL|HcL].
  - exists L. split; [exact Hl|]. split; [exact HcL|]. split; [exact HdL|].
    intros x Hx Hxc Hxd. destruct (Hall x Hx Hxd) as [E|E]; [congruence|exact E].
  - exfalso.
    assert (Hthreat : four_threat W L d).
    { unfold four_threat. split; [exact Hl|]. split; [exact HdL|]. split; [exact HdW|].
      intros x Hx Hxd. destruct (Hall x Hx Hxd) as [E|E]; [subst; contradiction|exact E]. }
    pose proof (threat_wins W L d Hthreat). congruence.
Qed.

Definition stem (L : list cell) (c d : cell) : list cell := without d (without c L).

Lemma stem_props : forall L c d W,
  In L all_lines -> In c L -> In d L -> d <> c ->
  (forall x, In x L -> x <> c -> x <> d -> In x W) ->
  length (stem L c d) = 3 /\ NoDup (stem L c d) /\ incl (stem L c d) W /\
  (forall x, In x (stem L c d) <-> In x L /\ x <> c /\ x <> d).
Proof.
  intros L c d W Hl Hc Hd Hdc Hall.
  destruct (winning_line_properties L Hl) as [Hlen Hnd].
  assert (Hmem : forall x, In x (stem L c d) <-> In x L /\ x <> c /\ x <> d).
  { intros x. unfold stem. rewrite !without_In. tauto. }
  assert (Hnd1 : NoDup (without c L)) by (apply NoDup_filter; exact Hnd).
  assert (Hd1 : In d (without c L)) by (apply without_In; auto).
  pose proof (without_length L c Hnd Hc) as H1.
  pose proof (without_length (without c L) d Hnd1 Hd1) as H2.
  split; [unfold stem; lia|]. split; [unfold stem; apply NoDup_filter; exact Hnd1|].
  split; [|exact Hmem].
  intros x Hx. apply Hmem in Hx as [Hx [Hxc Hxd]]. apply Hall; assumption.
Qed.

Lemma cover_by_big : forall (big W : list cell),
  NoDup big -> incl big W -> length W <= length big -> forall x, In x W -> In x big.
Proof.
  intros big W Hnd Hincl Hlen x Hx.
  destruct (in_dec Nat.eq_dec x big) as [H|H]; [exact H|exfalso].
  assert (Hnd' : NoDup (x :: big)) by (constructor; assumption).
  assert (Hincl' : incl (x :: big) W)
    by (intros y [Hy|Hy]; [subst; exact Hx|apply Hincl; exact Hy]).
  pose proof (NoDup_incl_length Hnd' Hincl') as Hl. cbn in Hl. lia.
Qed.

(** A fork cell with at most six White stones: all White stones lie on the
    two fork lines. *)
Lemma fork_structure : forall W c d1 d2,
  NoDup W -> length W <= 6 ->
  ~ In c W -> ~ In d1 W -> ~ In d2 W -> d1 <> c -> d2 <> c -> d1 <> d2 ->
  has_win (c :: W) = false -> has_win (d1 :: W) = false -> has_win (d2 :: W) = false ->
  has_win (d1 :: c :: W) = true -> has_win (d2 :: c :: W) = true ->
  exists L1 L2, In L1 all_lines /\ In L2 all_lines /\
    In c L1 /\ In c L2 /\ In d1 L1 /\ In d2 L2 /\
    (forall x, In x L1 -> x <> c -> x <> d1 -> In x W) /\
    (forall x, In x L2 -> x <> c -> x <> d2 -> In x W) /\
    (forall x, In x W -> In x L1 \/ In x L2).
Proof.
  intros W c d1 d2 HndW HlenW HcW Hd1W Hd2W Hd1c Hd2c Hd12 Hc Hd1 Hd2 Hw1 Hw2.
  destruct (fork_line W c d1 HcW Hd1W Hd1c Hc Hd1 Hw1) as [L1 [Hl1 [Hc1 [Hd1L Hall1]]]].
  destruct (fork_line W c d2 HcW Hd2W Hd2c Hc Hd2 Hw2) as [L2 [Hl2 [Hc2 [Hd2L Hall2]]]].
  exists L1, L2. do 8 (split; [assumption|]).
  assert (Hneq : L1 <> L2).
  { intros E. subst L2. apply Hd2W.
    apply Hall1; [exact Hd2L|exact Hd2c|intro E; apply Hd12; symmetry; exact E]. }
  destruct (stem_props L1 c d1 W Hl1 Hc1 Hd1L Hd1c Hall1) as [Hs1 [Hn1 [Hi1 Hm1]]].
  destruct (stem_props L2 c d2 W Hl2 Hc2 Hd2L Hd2c Hall2) as [Hs2 [Hn2 [Hi2 Hm2]]].
  assert (Hnd : NoDup (stem L1 c d1 ++ stem L2 c d2)).
  { apply NoDup_app; [exact Hn1|exact Hn2|].
    intros x Hx1 Hx2. apply Hm1 in Hx1 as [Hx1 [Hxc _]]. apply Hm2 in Hx2 as [Hx2 _].
    apply Hxc. exact (two_common_cells L1 L2 x c Hl1 Hl2 Hneq Hx1 Hx2 Hc1 Hc2). }
  assert (Hincl : incl (stem L1 c d1 ++ stem L2 c d2) W).
  { intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; [apply Hi1|apply Hi2]; exact Hx. }
  assert (Hlen : length W <= length (stem L1 c d1 ++ stem L2 c d2))
    by (rewrite length_app; lia).
  intros x Hx.
  pose proof (cover_by_big _ W Hnd Hincl Hlen x Hx) as Hin.
  apply in_app_iff in Hin as [Hin|Hin];
    [left; apply Hm1 in Hin|right; apply Hm2 in Hin]; tauto.
Qed.

(** Any further line with three White stones is one of the two fork lines. *)
Lemma third_line : forall M L1 L2 SM,
  In M all_lines -> In L1 all_lines -> In L2 all_lines ->
  NoDup SM -> incl SM M -> (forall x, In x SM -> In x L1 \/ In x L2) -> 3 <= length SM ->
  M = L1 \/ M = L2.
Proof.
  intros M L1 L2 SM Hm Hl1 Hl2 Hnd Hincl Hcov Hlen.
  destruct (list_eq_dec Nat.eq_dec M L1) as [E|N1]; [left; exact E|].
  destruct (list_eq_dec Nat.eq_dec M L2) as [E|N2]; [right; exact E|exfalso].
  pose proof (filter_lengths_partition (fun x => existsb (Nat.eqb x) L1) SM) as Hpart.
  assert (HA : length (filter (fun x => existsb (Nat.eqb x) L1) SM) <= 1).
  { assert (Hi : incl (filter (fun x => existsb (Nat.eqb x) L1) SM) (intersection M L1)).
    { intros x Hx. apply filter_In in Hx as [Hx Hf]. unfold intersection. apply filter_In.
      split; [apply Hincl; exact Hx|exact Hf]. }
    exact (Nat.le_trans _ _ _ (NoDup_incl_length (NoDup_filter _ Hnd) Hi)
             (winning_lines_linear M L1 Hm Hl1 N1)). }
  assert (HB : length (filter (fun x => negb (existsb (Nat.eqb x) L1)) SM) <= 1).
  { assert (Hi : incl (filter (fun x => negb (existsb (Nat.eqb x) L1)) SM) (intersection M L2)).
    { intros x Hx. apply filter_In in Hx as [Hx Hf]. cbv beta in Hf.
      unfold intersection. apply filter_In.
      split; [apply Hincl; exact Hx|].
      apply member_spec. destruct (Hcov x Hx) as [H|H]; [|exact H].
      exfalso. apply negb_true_iff in Hf. apply member_spec in H. congruence. }
    exact (Nat.le_trans _ _ _ (NoDup_incl_length (NoDup_filter _ Hnd) Hi)
             (winning_lines_linear M L2 Hm Hl2 N2)). }
  assert (Hs : length SM <= 1 + 1)
    by exact (eq_ind _ (fun n => n <= 1 + 1) (Nat.add_le_mono _ _ _ _ HA HB) _ Hpart).
  lia.
Qed.

(** * 2. Game facts *)

Lemma legal_after_black : forall st r x,
  is_legal_move (move_state false st r) x = true ->
  is_legal_move st x = true /\ x <> effective_move st r.
Proof.
  intros st r x H. split; [apply legal_before_black_move with (request := r); exact H|].
  destruct (legal_move_fresh _ _ H) as [_ [_ HB]].
  change (~ In x (effective_move st r :: black_stones st)) in HB.
  intros E. apply HB. left. symmetry. exact E.
Qed.

Lemma legal_after_white : forall st r x,
  is_legal_move (move_state true st r) x = true ->
  is_legal_move st x = true /\ x <> effective_move st r.
Proof.
  intros st r x H. destruct (legal_move_fresh _ _ H) as [Hb [HW HB]].
  change (~ In x (effective_move st r :: white_stones st)) in HW.
  change (~ In x (black_stones st)) in HB.
  split.
  - unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hb|].
    apply negb_true_iff. destruct (occupied st x) eqn:Hocc; [|reflexivity].
    apply occupied_spec in Hocc. apply in_app_iff in Hocc as [Hi|Hi]; exfalso;
      [apply HW; right; exact Hi|apply HB; exact Hi].
  - intros E. apply HW. left. symmetry. exact E.
Qed.

Lemma in_all_cells : forall st c, is_legal_move st c = true -> In c all_cells.
Proof.
  intros st c H. destruct (legal_move_fresh st c H) as [Hb _].
  unfold all_cells. apply in_seq. lia.
Qed.

Lemma legal_not_white : forall st c, is_legal_move st c = true -> ~ In c (white_stones st).
Proof. intros st c H. destruct (legal_move_fresh st c H) as [_ [H1 _]]. exact H1. Qed.

Lemma effective_legal : forall st c, is_legal_move st c = true -> effective_move st c = c.
Proof. intros st c H. unfold effective_move. rewrite H. reflexivity. Qed.

(** * 3. The policy *)

Definition fork_cellb (st : GameState) (c : cell) : bool :=
  is_legal_move st c &&
  (1 <? length (filter (fun d => negb (d =? c) && is_legal_move st d &&
                                 has_win (d :: c :: white_stones st)) all_cells)).

Definition cross_policy : BlackStrategy := fun st =>
  match find (white_completionb st) all_cells with
  | Some c => c
  | None => match find (fork_cellb st) all_cells with
            | Some c => c
            | None => 0
            end
  end.

(** White to move: no cell gives White two distinct completion cells. *)
Definition no_fork (st : GameState) : Prop := forall c d1 d2,
  is_legal_move st c = true -> is_legal_move st d1 = true -> is_legal_move st d2 = true ->
  d1 <> c -> d2 <> c ->
  has_win (d1 :: c :: white_stones st) = true ->
  has_win (d2 :: c :: white_stones st) = true -> d1 = d2.

Lemma cross_policy_safe : forall st,
  (forall x y, white_completionb st x = true -> white_completionb st y = true -> x = y) ->
  white_next_safe (move_state false st (cross_policy st)).
Proof.
  intros st Huniq c Hlegal.
  destruct (has_win (c :: white_stones (move_state false st (cross_policy st)))) eqn:Hwin;
    [|reflexivity].
  exfalso.
  assert (Hnext : white_completionb (move_state false st (cross_policy st)) c = true).
  { unfold white_completionb. rewrite Hlegal, Hwin. reflexivity. }
  apply completion_before_black_move in Hnext.
  destruct (legal_after_black st (cross_policy st) c Hlegal) as [Hold Hne].
  unfold cross_policy in Hne.
  destruct (find (white_completionb st) all_cells) as [t|] eqn:Hf.
  - apply find_some in Hf as [_ Ht].
    pose proof (Huniq c t Hnext Ht) as E. subst t.
    unfold white_completionb in Ht. apply andb_true_iff in Ht as [Htl _].
    rewrite (effective_legal st c Htl) in Hne. congruence.
  - pose proof (@find_none cell _ _ Hf c (in_all_cells st c Hold)). congruence.
Qed.

Lemma length_member : forall (l : list cell), (1 <? length l) = true -> exists e, In e l.
Proof. intros [|e l] H; [discriminate|exists e; left; reflexivity]. Qed.

(** The key step: with at most six White stones, one Black move by
    [cross_policy] leaves no fork cell. *)
Lemma cross_policy_no_fork : forall st,
  valid_state st -> has_win (white_stones st) = false -> length (white_stones st) <= 6 ->
  white_next_safe (move_state false st (cross_policy st)) ->
  no_fork (move_state false st (cross_policy st)).
Proof.
  intros st Hvalid Hquiet Hsmall Hsafe c d1 d2 Hc Hd1 Hd2 Hd1c Hd2c Hw1 Hw2.
  destruct (Nat.eq_dec d1 d2) as [E|Hd12]; [exact E|exfalso].
  change (has_win (d1 :: c :: white_stones st) = true) in Hw1.
  change (has_win (d2 :: c :: white_stones st) = true) in Hw2.
  pose proof (Hsafe c Hc) as Hcq. pose proof (Hsafe d1 Hd1) as Hd1q.
  pose proof (Hsafe d2 Hd2) as Hd2q.
  change (has_win (c :: white_stones st) = false) in Hcq.
  change (has_win (d1 :: white_stones st) = false) in Hd1q.
  change (has_win (d2 :: white_stones st) = false) in Hd2q.
  destruct (legal_after_black st (cross_policy st) c Hc) as [Hc0 Hcb].
  destruct (legal_after_black st (cross_policy st) d1 Hd1) as [Hd10 Hd1b].
  destruct (legal_after_black st (cross_policy st) d2 Hd2) as [Hd20 Hd2b].
  pose proof (legal_not_white st c Hc0) as HcW.
  pose proof (legal_not_white st d1 Hd10) as Hd1W.
  pose proof (legal_not_white st d2 Hd20) as Hd2W.
  pose proof (valid_white_nodup st Hvalid) as HndW.
  destruct (fork_structure (white_stones st) c d1 d2 HndW Hsmall HcW Hd1W Hd2W
              Hd1c Hd2c Hd12 Hcq Hd1q Hd2q Hw1 Hw2)
    as [L1 [L2 [Hl1 [Hl2 [Hc1 [Hc2 [Hd1L [Hd2L [Hall1 [Hall2 Hcov]]]]]]]]]].
  unfold cross_policy in Hcb, Hd1b, Hd2b.
  destruct (find (white_completionb st) all_cells) as [t|] eqn:Hf.
  - (* Black blocked a threat at [t]: that threat would need four White
       stones outside the two fork lines' shared structure. *)
    apply find_some in Hf as [_ Ht].
    unfold white_completionb in Ht. apply andb_true_iff in Ht as [Htl Htw].
    rewrite (effective_legal st t Htl) in Hcb.
    destruct (added_win_gives_threat _ t Hquiet (legal_not_white st t Htl) Htw) as [T HT].
    destruct (threat_support _ T t HT) as [HlenT [HndT HinclT]].
    destruct HT as [HTl [HtT [_ _]]].
    assert (HsubT : incl (without t T) T)
      by (intros x Hx; apply without_In in Hx; tauto).
    destruct (third_line T L1 L2 (without t T) HTl Hl1 Hl2 HndT HsubT
                (fun x Hx => Hcov x (HinclT x Hx)) ltac:(lia)) as [E|E]; subst T;
      apply HcW, HinclT, without_In; split; [exact Hc1|exact Hcb|exact Hc2|exact Hcb].
  - destruct (find (fork_cellb st) all_cells) as [f|] eqn:Hg.
    + (* Black took the fork cell [f]: its fork line must be L1 or L2, so [f]
         would be White. *)
      apply find_some in Hg as [_ Hfk].
      unfold fork_cellb in Hfk. apply andb_true_iff in Hfk as [Hfl Hcount].
      rewrite (effective_legal st f Hfl) in Hcb, Hd1b, Hd2b.
      destruct (length_member _ Hcount) as [e He].
      apply filter_In in He as [_ HeP].
      apply andb_true_iff in HeP as [HeP Hew]. apply andb_true_iff in HeP as [Hef Hel].
      apply negb_true_iff, Nat.eqb_neq in Hef.
      pose proof (@find_none cell _ _ Hf f (in_all_cells st f Hfl)) as Hnf.
      pose proof (@find_none cell _ _ Hf e (in_all_cells st e Hel)) as Hne.
      unfold white_completionb in Hnf, Hne. rewrite Hfl in Hnf. rewrite Hel in Hne.
      cbn [andb] in Hnf, Hne.
      destruct (fork_line (white_stones st) f e (legal_not_white st f Hfl)
                  (legal_not_white st e Hel) Hef Hnf Hne Hew)
        as [M [HMl [HfM [HeM HMall]]]].
      destruct (stem_props M f e _ HMl HfM HeM Hef HMall) as [Hs [Hn [Hi Hm]]].
      assert (HsubM : incl (stem M f e) M) by (intros x Hx; apply Hm in Hx; tauto).
      destruct (third_line M L1 L2 (stem M f e) HMl Hl1 Hl2 Hn HsubM
                  (fun x Hx => Hcov x (Hi x Hx)) ltac:(lia)) as [E|E]; subst M.
      * apply (legal_not_white st f Hfl), Hall1;
          [exact HfM|intro E; apply Hcb; symmetry; exact E|intro E; apply Hd1b; symmetry; exact E].
      * apply (legal_not_white st f Hfl), Hall2;
          [exact HfM|intro E; apply Hcb; symmetry; exact E|intro E; apply Hd2b; symmetry; exact E].
    + (* Black saw no fork cell, yet [c] is one. *)
      assert (Hfork : fork_cellb st c = true).
      { unfold fork_cellb. rewrite Hc0. cbn [andb]. apply Nat.ltb_lt.
        assert (Hincl : incl [d1; d2]
          (filter (fun d => negb (d =? c) && is_legal_move st d &&
                            has_win (d :: c :: white_stones st)) all_cells)).
        { intros z [Hz|[Hz|[]]]; subst z; apply filter_In;
            (split; [apply (in_all_cells st); assumption|]); cbv beta;
            apply andb_true_iff; (split; [apply andb_true_iff; split|assumption]);
            try assumption; apply negb_true_iff, Nat.eqb_neq; assumption. }
        assert (Hnd2 : NoDup [d1; d2]).
        { constructor; [intros [H|[]]; congruence|constructor; [intros []|constructor]]. }
        pose proof (NoDup_incl_length Hnd2 Hincl) as Hl. cbn in Hl. lia. }
      pose proof (@find_none cell _ _ Hg c (in_all_cells st c Hc0)). congruence.
Qed.

(** Before White's 7th move there is no fork cell, so after it the
    completion cell is unique. *)
Lemma no_fork_unique : forall st r,
  valid_state st -> length (history st) < 125 -> no_fork st ->
  forall x y, white_completionb (move_state true st r) x = true ->
  white_completionb (move_state true st r) y = true -> x = y.
Proof.
  intros st r Hvalid Hlen Hnf x y Hx Hy.
  unfold white_completionb in Hx, Hy.
  apply andb_true_iff in Hx as [Hxl Hxw]. apply andb_true_iff in Hy as [Hyl Hyw].
  destruct (legal_after_white st r x Hxl) as [Hx0 Hxe].
  destruct (legal_after_white st r y Hyl) as [Hy0 Hye].
  change (has_win (x :: effective_move st r :: white_stones st) = true) in Hxw.
  change (has_win (y :: effective_move st r :: white_stones st) = true) in Hyw.
  exact (Hnf (effective_move st r) x y (effective_move_is_legal st r Hvalid Hlen)
           Hx0 Hy0 Hxe Hye Hxw Hyw).
Qed.

(** * 4. The opening bound *)

Lemma cross_prefix : forall rounds st w,
  length (white_stones st) + rounds <= 8 ->
  2 * rounds + length (history st) <= 125 -> valid_state st ->
  (rounds = 0 \/ (white_next_safe st /\ (length (white_stones st) <= 6 -> no_fork st))) ->
  outcome (step_game (2 * rounds) true st w cross_policy) <> WhiteWins.
Proof.
  induction rounds as [|rounds IH]; intros st w Hcount Hlen Hvalid Hinv; [discriminate|].
  destruct Hinv as [Hzero|[Hsafe Hnf]]; [discriminate|].
  replace (2 * S rounds) with (S (S (2 * rounds))) by lia.
  rewrite step_game_equation. cbn zeta.
  set (after_white := move_state true st (w st)).
  assert (Hwhite_len : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  assert (Hwhite_count : length (white_stones after_white) = S (length (white_stones st)))
    by reflexivity.
  assert (Hwhite_valid : valid_state after_white) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hwhite_nowin : has_win (white_stones after_white) = false).
  { apply Hsafe, effective_move_is_legal; [exact Hvalid|lia]. }
  unfold move_result at 1. rewrite Hwhite_nowin.
  destruct (length (history after_white) =? 125); [discriminate|].
  rewrite step_game_equation. cbn zeta.
  change (outcome
    (let next := move_state false after_white (cross_policy after_white) in
     match move_result false next with
     | Some r => make_trace next r
     | None => step_game (2 * rounds) true next w cross_policy
     end) <> WhiteWins).
  set (after_black := move_state false after_white (cross_policy after_white)).
  cbv zeta. unfold move_result.
  destruct (has_win (black_stones after_black)); [discriminate|].
  destruct (length (history after_black) =? 125); [discriminate|].
  apply IH.
  - change (length (white_stones after_white) + rounds <= 8). rewrite Hwhite_count. lia.
  - unfold after_black. rewrite move_state_history, Hwhite_len. lia.
  - apply move_preserves_validity; [exact Hwhite_valid|lia].
  - destruct rounds as [|rounds]; [left; reflexivity|]. right.
    assert (Hsafe' : white_next_safe after_black).
    { apply cross_policy_safe. intros x y Hx Hy.
      destruct (Nat.lt_ge_cases (length (white_stones after_white)) 7) as [Hlt|Hge].
      - exact (white_completion_unique_below_seven after_white x y Hwhite_nowin Hlt Hx Hy).
      - exact (no_fork_unique st (w st) Hvalid ltac:(lia) (Hnf ltac:(lia)) x y Hx Hy). }
    split; [exact Hsafe'|].
    intros Hsmall. apply cross_policy_no_fork;
      [exact Hwhite_valid|exact Hwhite_nowin|exact Hsmall|exact Hsafe'].
Qed.

Lemma initial_no_fork : no_fork initial_state.
Proof.
  intros c d1 d2 _ _ _ _ _ Hw _.
  rewrite short_stones_no_win in Hw; [discriminate|cbn; lia].
Qed.

Theorem cross_policy_no_white_win_in_sixteen_plies : forall w,
  outcome (step_game 16 true initial_state w cross_policy) <> WhiteWins.
Proof.
  intros w. apply (cross_prefix 8 initial_state w);
    [reflexivity|cbn; lia|apply initial_state_valid|].
  right. split; [apply initial_white_next_safe|intros _; apply initial_no_fork].
Qed.

Theorem cross_policy_delays_white_win_until_ply_seventeen : forall w,
  outcome (play w cross_policy) = WhiteWins ->
  17 <= length (history (final_state (play w cross_policy))).
Proof.
  intros w Hwin. unfold play in Hwin |- *.
  destruct (white_win_visible_or_later 16 125 true initial_state w cross_policy
    ltac:(lia) Hwin) as [Hearly|Hlate].
  - exfalso. exact (cross_policy_no_white_win_in_sixteen_plies w Hearly).
  - exact Hlate.
Qed.

Print Assumptions cross_policy_delays_white_win_until_ply_seventeen.
