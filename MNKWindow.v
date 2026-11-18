(** **************************************************************************
    MNKWindow.v: The Window Simulation Theorem
    (a CORRECT replacement for the former "Subgrid Monotone Projection")

    Playing a small-board strategy inside a corner window of a larger board is
    NOT automatically sound in the strong game: lines that cross the window
    boundary can be completed by Player 2 (see MNKPhaseTransition.v for a
    concrete refutation of the old projection argument on 3 x 5).

    This file proves a sound version.  Fix an R x C window in the top-left
    corner of an m x n board (R <= m, C <= n).  In the WINDOW GAME:
      - Player 1 moves inside the window and wins with a line of the window;
      - Player 2 replies inside the window, or "far" (anywhere outside), which
        the window game records only as a counter [far];
      - Player 2 is conservatively deemed to have WON as soon as it owns a
        window line, or far >= 1 and far + (P2 stones on edge cells) >= k,
        where the edge cells are those within k-1 rows/columns of a side of
        the window that borders the rest of the board.
    Theorem [window_certificate_lifts]: a window certificate accepted by the
    decidable checker [wcheck] yields [forces_win (gen_lines m n k) P1 d] on
    the empty m x n board, for EVERY m >= R and n >= C.

    Zero axioms, zero admissions (closed under the global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool PeanoNat.
Import ListNotations.
Require Import MNK.MNKBoard.
Require Import MNK.MNKGame.
Require Import MNK.MNKCertChecker.

Section Window.

Variables (R C k : nat) (rowfar colfar : bool).

Definition wlines : list (list nat) := gen_lines R C k.

(** Key used in a certificate for the "far" (outside the window) reply. *)
Definition pass_key : nat := R * C.

(** Edge cells of the window: a line that leaves the window can only meet
    the window in these cells. *)
Definition edge (i : nat) : bool :=
  (rowfar && (R <? i / C + k)) || (colfar && (C <? i mod C + k)).

Definition edge_p2 (wb : board_t) : nat :=
  length (filter (fun i => edge i && cell_owned_by wb P2 i) (seq 0 (R * C))).

Definition danger (wb : board_t) (far : nat) : bool :=
  check_win wb P2 wlines || ((1 <=? far) && (k <=? far + edge_p2 wb)).

Fixpoint wcheck (d : nat) (wb : board_t) (far : nat) (ct : cert) {struct ct} : bool :=
  match ct with
  | Imm m =>
      match d with
      | 0 => false
      | S _ => is_legal_move wb m && check_win (set_cell wb m P1) P1 wlines
      end
  | Br m bs =>
      match d with
      | 0 => false
      | S d' =>
          let wb1 := set_cell wb m P1 in
          is_legal_move wb m &&
          nonempty (legal_moves wb1) &&
          forallb (fun c => has_key c bs) (legal_moves wb1) &&
          has_key pass_key bs &&
          wcheck_br d' wb1 far bs
      end
  end
with wcheck_br (d : nat) (wb1 : board_t) (far : nat) (bs : branches) {struct bs} : bool :=
  match bs with
  | BNil => true
  | BCons c sub rest =>
      (if c =? pass_key
       then negb (danger wb1 (S far)) && wcheck d wb1 (S far) sub
       else is_legal_move wb1 c && negb (danger (set_cell wb1 c P2) far) &&
            wcheck d (set_cell wb1 c P2) far sub)
      && wcheck_br d wb1 far rest
  end.

Lemma wcheck_br_spec : forall bs d wb1 far,
  wcheck_br d wb1 far bs = true ->
  forall c sub, InB c sub bs ->
    (c = pass_key /\ danger wb1 (S far) = false /\ wcheck d wb1 (S far) sub = true) \/
    (c <> pass_key /\ is_legal_move wb1 c = true /\
     danger (set_cell wb1 c P2) far = false /\ wcheck d (set_cell wb1 c P2) far sub = true).
Proof.
  induction bs as [| c' s rest IH]; intros d wb1 far H c sub Hin; simpl in *; [contradiction |].
  apply andb_true_iff in H as [Hhd Hrest].
  destruct Hin as [[-> ->] | Hin]; [| eapply IH; eauto].
  destruct (c' =? pass_key) eqn:E.
  - apply Nat.eqb_eq in E. left. apply andb_true_iff in Hhd as [Hd Hw].
    apply negb_true_iff in Hd. auto.
  - apply Nat.eqb_neq in E. right.
    apply andb_true_iff in Hhd as [Hhd Hw]. apply andb_true_iff in Hhd as [Hl Hd].
    apply negb_true_iff in Hd. auto.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** The real m x n board and its relation to the window                    *)
(* ------------------------------------------------------------------------- *)

Variables (m n : nat).
Hypothesis HC : 0 < C.
Hypothesis HRm : R <= m.
Hypothesis HCn : C <= n.
Hypothesis Hk : 1 <= k.
Hypothesis Hrow : R < m -> rowfar = true.
Hypothesis Hcol : C < n -> colfar = true.

Definition inW (x : nat) : bool := (x / n <? R) && (x mod n <? C).
Definition toW (x : nat) : nat := (x / n) * C + x mod n.
Definition ofW (i : nat) : nat := (i / C) * n + i mod C.

Lemma Hn : 0 < n.
Proof. lia. Qed.

Lemma ofW_lt : forall i, i < R * C -> ofW i < m * n.
Proof.
  intros i Hi. unfold ofW.
  assert (i / C < R) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (i mod C < C) by (apply Nat.mod_upper_bound; lia).
  nia.
Qed.

Lemma ofW_div : forall i, (ofW i) / n = i / C.
Proof.
  intros i. unfold ofW. apply idx_div.
  assert (i mod C < C) by (apply Nat.mod_upper_bound; lia). lia.
Qed.

Lemma ofW_mod : forall i, (ofW i) mod n = i mod C.
Proof.
  intros i. unfold ofW. apply idx_mod.
  assert (i mod C < C) by (apply Nat.mod_upper_bound; lia). lia.
Qed.

Lemma toW_ofW : forall i, toW (ofW i) = i.
Proof.
  intros i. unfold toW. rewrite ofW_div, ofW_mod.
  rewrite (Nat.div_mod_eq i C) at 3. lia.
Qed.

Lemma inW_ofW : forall i, i < R * C -> inW (ofW i) = true.
Proof.
  intros i Hi. unfold inW. rewrite ofW_div, ofW_mod.
  apply andb_true_iff. split; apply Nat.ltb_lt.
  - apply Nat.Div0.div_lt_upper_bound. lia.
  - apply Nat.mod_upper_bound. lia.
Qed.

Lemma inW_spec : forall x, inW x = true <-> x / n < R /\ x mod n < C.
Proof.
  intros x. unfold inW. rewrite andb_true_iff, !Nat.ltb_lt. tauto.
Qed.

Lemma toW_div : forall x, inW x = true -> (toW x) / C = x / n.
Proof. intros x H. apply inW_spec in H. unfold toW. apply idx_div. lia. Qed.

Lemma toW_mod : forall x, inW x = true -> (toW x) mod C = x mod n.
Proof. intros x H. apply inW_spec in H. unfold toW. apply idx_mod. lia. Qed.

Lemma ofW_toW : forall x, inW x = true -> ofW (toW x) = x.
Proof.
  intros x H. unfold ofW. rewrite toW_div, toW_mod by exact H.
  rewrite (Nat.div_mod_eq x n) at 3. lia.
Qed.

Lemma toW_lt : forall x, inW x = true -> toW x < R * C.
Proof.
  intros x H. apply inW_spec in H. unfold toW. nia.
Qed.

Definition rel (B wb : board_t) (F : list nat) : Prop :=
  length B = m * n /\ length wb = R * C /\
  (forall i, i < R * C -> get_cell B (ofW i) = get_cell wb i) /\
  (forall x, inW x = false -> get_cell B x = Some P2 -> In x F).

Lemma rel_empty : rel (empty_board (m * n)) (empty_board (R * C)) [].
Proof.
  repeat split.
  - apply empty_board_length.
  - apply empty_board_length.
  - intros i _. rewrite !get_cell_empty_board. reflexivity.
  - intros x _ H. rewrite get_cell_empty_board in H. discriminate.
Qed.

Lemma rel_get : forall B wb F x, rel B wb F -> inW x = true ->
  get_cell wb (toW x) = get_cell B x.
Proof.
  intros B wb F x (_ & _ & Hb & _) Hx.
  rewrite <- (Hb (toW x) (toW_lt x Hx)). rewrite ofW_toW by exact Hx. reflexivity.
Qed.

Lemma rel_set_in : forall B wb F i pl, rel B wb F -> i < R * C ->
  rel (set_cell B (ofW i) pl) (set_cell wb i pl) F.
Proof.
  intros B wb F i pl (HlB & Hlw & Hb & Hf) Hi.
  repeat split.
  - rewrite set_cell_length. exact HlB.
  - rewrite set_cell_length. exact Hlw.
  - intros j Hj. destruct (Nat.eq_dec i j) as [-> | Hij].
    + rewrite !get_set_cell_same; [reflexivity | lia |].
      rewrite HlB. apply ofW_lt. exact Hj.
    + rewrite !get_set_cell_other; [apply Hb; exact Hj | exact Hij |].
      intros E. apply Hij. rewrite <- (toW_ofW i), <- (toW_ofW j), E. reflexivity.
  - intros x Hx Hp. rewrite get_set_cell_other in Hp; [apply Hf; auto |].
    intros E. subst x. rewrite inW_ofW in Hx by exact Hi. discriminate.
Qed.

Lemma rel_set_out : forall B wb F y, rel B wb F -> inW y = false ->
  rel (set_cell B y P2) wb (y :: F).
Proof.
  intros B wb F y (HlB & Hlw & Hb & Hf) Hy.
  repeat split.
  - rewrite set_cell_length. exact HlB.
  - exact Hlw.
  - intros j Hj. rewrite get_set_cell_other; [apply Hb; exact Hj |].
    intros E. rewrite E, inW_ofW in Hy by exact Hj. discriminate.
  - intros x Hx Hp. destruct (Nat.eq_dec y x) as [-> | Hyx]; [left; reflexivity |].
    right. rewrite get_set_cell_other in Hp by exact Hyx. apply Hf; auto.
Qed.

Lemma rel_legal_ofW : forall B wb F i, rel B wb F ->
  is_legal_move wb i = true -> is_legal_move B (ofW i) = true.
Proof.
  intros B wb F i Hr Hi. destruct Hr as (HlB & Hlw & Hb & _).
  pose proof (legal_move_lt wb i Hi) as Hlt. rewrite Hlw in Hlt.
  apply legal_move_intro.
  - rewrite HlB. apply ofW_lt. exact Hlt.
  - rewrite Hb by exact Hlt. apply legal_move_empty. exact Hi.
Qed.

Lemma rel_legal_toW : forall B wb F x, rel B wb F -> inW x = true ->
  is_legal_move B x = true -> is_legal_move wb (toW x) = true.
Proof.
  intros B wb F x Hr Hx Hl. apply legal_move_intro.
  - destruct Hr as (_ & Hlw & _). rewrite Hlw. apply toW_lt. exact Hx.
  - rewrite (rel_get B wb F x Hr Hx). apply legal_move_empty. exact Hl.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** Geometry: lines of the window vs. lines of the board                    *)
(* ------------------------------------------------------------------------- *)

Lemma fits_mono : forall d r c, fits R C k d r c -> fits m n k d r c.
Proof. intros d r c H. destruct d; simpl in *; lia. Qed.

Lemma cell_at_lt_C : forall d r c i, fits R C k d r c -> i < k ->
  snd (cell_at k d r c i) < C.
Proof. intros. pose proof (cell_at_bounds R C k d r c i H H0). lia. Qed.

(** Every window line is a line of the big board. *)
Lemma embed_window_line : forall Lw, In Lw wlines -> In (map ofW Lw) (gen_lines m n k).
Proof.
  intros Lw HL. apply in_gen_lines in HL as (d & r & c & Hf & ->).
  apply in_gen_lines. exists d, r, c. split; [apply fits_mono; exact Hf |].
  unfold mkline. rewrite map_map. apply map_ext_in. intros i Hi.
  apply in_seq in Hi.
  pose proof (cell_at_lt_C d r c i Hf ltac:(lia)) as Hc.
  unfold ofW. rewrite idx_div, idx_mod by exact Hc. reflexivity.
Qed.

(** A board line lying entirely inside the window is a window line. *)
Lemma restrict_board_line : forall L, In L (gen_lines m n k) ->
  (forall x, In x L -> inW x = true) -> In (map toW L) wlines.
Proof.
  intros L HL Hin. apply in_gen_lines in HL as (d & r & c & Hf & ->).
  assert (Hcell : forall i, i < k ->
    fst (cell_at k d r c i) < R /\ snd (cell_at k d r c i) < C).
  { intros i Hi. pose proof (cell_at_bounds m n k d r c i Hf Hi) as B.
    assert (Hx : In (fst (cell_at k d r c i) * n + snd (cell_at k d r c i))
                    (mkline n k d r c)) by (apply in_mkline; exists i; auto).
    apply Hin, inW_spec in Hx. rewrite idx_div, idx_mod in Hx by lia. exact Hx. }
  assert (Hf' : fits R C k d r c).
  { pose proof (Hcell 0 ltac:(lia)) as H0. pose proof (Hcell (k - 1) ltac:(lia)) as H1.
    pose proof (cell_at_bounds m n k d r c 0 Hf ltac:(lia)).
    destruct d; simpl in *; lia. }
  unfold wlines. apply in_gen_lines. exists d, r, c. split; [exact Hf' |].
  unfold mkline. rewrite map_map. apply map_ext_in. intros i Hi.
  apply in_seq in Hi. pose proof (cell_at_bounds m n k d r c i Hf ltac:(lia)) as B.
  unfold toW. rewrite idx_div, idx_mod by lia. reflexivity.
Qed.

(** If a board line leaves the window, its cells inside the window are edge cells. *)
Lemma crossing_line_edge : forall L x0 y, In L (gen_lines m n k) ->
  In x0 L -> inW x0 = false -> In y L -> inW y = true -> edge (toW y) = true.
Proof.
  intros L x0 y HL Hx0 Hout Hy Hiny.
  pose proof (gen_lines_bounding_box m n k L x0 y HL Hx0 Hy) as [Br Bc].
  pose proof (gen_lines_in_range m n k L x0 HL Hx0) as Hr.
  assert (Hxr : x0 / n < m) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hxc : x0 mod n < n) by (apply Nat.mod_upper_bound; lia).
  unfold edge. rewrite toW_div, toW_mod by exact Hiny.
  unfold inW in Hout. apply andb_false_iff in Hout as [Ho | Ho]; apply Nat.ltb_ge in Ho.
  - rewrite Hrow by lia. apply orb_true_iff. left. apply andb_true_iff.
    split; [reflexivity | apply Nat.ltb_lt; lia].
  - rewrite Hcol by lia. apply orb_true_iff. right. apply andb_true_iff.
    split; [reflexivity | apply Nat.ltb_lt; lia].
Qed.

Lemma forallb_false_ex : forall (f : nat -> bool) (l : list nat),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros f l. induction l as [| a l IH]; simpl; [discriminate |].
  intros H. destruct (f a) eqn:E.
  - destruct (IH H) as [x [Hx Hf]]. exists x. auto.
  - exists a. auto.
Qed.

Lemma filter_partition_length : forall (f : nat -> bool) (l : list nat),
  length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
Proof.
  intros f l. induction l as [| a l IH]; simpl; [reflexivity |].
  destruct (f a); simpl; lia.
Qed.

(** Detection: whenever Player 2 owns a line of the big board, the window
    game's (conservative) danger test fires. *)
Lemma danger_detects : forall B wb F, rel B wb F ->
  check_win B P2 (gen_lines m n k) = true -> danger wb (length F) = true.
Proof.
  intros B wb F Hr Hw. apply check_win_iff in Hw as [L [HL Hown]].
  unfold danger. apply orb_true_iff.
  destruct (forallb inW L) eqn:Hall.
  - (* the line lies inside the window *)
    left. rewrite forallb_forall in Hall. apply check_win_iff.
    exists (map toW L). split; [apply restrict_board_line; auto |].
    intros i Hi. apply in_map_iff in Hi as [x [<- Hx]].
    rewrite (rel_get B wb F x Hr (Hall x Hx)). apply Hown. exact Hx.
  - (* the line leaves the window *)
    right. apply forallb_false_ex in Hall as [x0 [Hx0 Hout]].
    set (Li := filter inW L). set (Lo := filter (fun x => negb (inW x)) L).
    assert (HndL : NoDup L) by (eapply gen_lines_nodup; eauto).
    assert (Hpart : length Li + length Lo = k).
    { unfold Li, Lo. rewrite filter_partition_length. eapply gen_lines_uniform; eauto. }
    assert (HLo : length Lo <= length F).
    { apply NoDup_incl_length; [apply NoDup_filter; exact HndL |].
      intros x Hx. unfold Lo in Hx. apply filter_In in Hx as [Hx Hn'].
      apply negb_true_iff in Hn'. destruct Hr as (_ & _ & _ & Hf).
      apply Hf; auto. }
    assert (HLo1 : 1 <= length Lo).
    { destruct Lo as [| a Lo'] eqn:E; simpl; [| lia].
      assert (In x0 Lo) by (unfold Lo; apply filter_In; split; [auto | rewrite Hout; reflexivity]).
      rewrite E in H. destruct H. }
    assert (HLi : length Li <= edge_p2 wb).
    { unfold edge_p2. rewrite <- (length_map toW Li).
      apply NoDup_incl_length.
      - apply NoDup_map_NoDup_ForallPairs; [| apply NoDup_filter; exact HndL].
        intros a b Ha Hb E. unfold Li in Ha, Hb.
        apply filter_In in Ha as [_ Ha]. apply filter_In in Hb as [_ Hb].
        rewrite <- (ofW_toW a Ha), <- (ofW_toW b Hb), E. reflexivity.
      - intros i Hi. apply in_map_iff in Hi as [x [<- Hx]].
        unfold Li in Hx. apply filter_In in Hx as [HxL Hxin].
        apply filter_In. split.
        + apply in_seq. pose proof (toW_lt x Hxin). lia.
        + apply andb_true_iff. split.
          * apply (crossing_line_edge L x0 x HL Hx0 Hout HxL Hxin).
          * apply cell_owned_iff. rewrite (rel_get B wb F x Hr Hxin). apply Hown. exact HxL. }
    apply andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** The simulation theorem                                                  *)
(* ------------------------------------------------------------------------- *)

Theorem wcheck_sound : forall ct d wb F B,
  rel B wb F -> wcheck d wb (length F) ct = true ->
  forces_win (gen_lines m n k) P1 d B.
Proof.
  apply (cert_mut
    (fun ct => forall d wb F B, rel B wb F -> wcheck d wb (length F) ct = true ->
       forces_win (gen_lines m n k) P1 d B)
    (fun bs => forall c sub, InB c sub bs -> forall d wb F B,
       rel B wb F -> wcheck d wb (length F) sub = true ->
       forces_win (gen_lines m n k) P1 d B)).
  - (* Imm: Player 1 completes a window line, which is a board line *)
    intros mv d wb F B Hr H. destruct d as [| d]; simpl in H; [discriminate |].
    apply andb_true_iff in H as [Hm Hw].
    pose proof (legal_move_lt wb mv Hm) as Hlt.
    assert (Hlt' : mv < R * C) by (destruct Hr as (_ & Hlw & _); lia).
    apply fw_now with (m := ofW mv); [eapply rel_legal_ofW; eauto |].
    apply check_win_iff in Hw as [Lw [HLw Hown]].
    apply check_win_iff. exists (map ofW Lw). split; [apply embed_window_line; exact HLw |].
    intros y Hy. apply in_map_iff in Hy as [i [<- Hi]].
    pose proof (gen_lines_in_range R C k Lw i HLw Hi) as Hir.
    destruct (rel_set_in B wb F mv P1 Hr Hlt') as (_ & _ & Hb & _).
    rewrite Hb by exact Hir. apply Hown. exact Hi.
  - (* Br *)
    intros mv bs IHbs d wb F B Hr H. destruct d as [| d]; simpl in H; [discriminate |].
    apply andb_true_iff in H as [H Hbr].
    apply andb_true_iff in H as [H Hpass].
    apply andb_true_iff in H as [H Hcov].
    apply andb_true_iff in H as [Hm Hne].
    rewrite forallb_forall in Hcov.
    pose proof (legal_move_lt wb mv Hm) as Hlt.
    assert (Hlt' : mv < R * C) by (destruct Hr as (_ & Hlw & _); lia).
    pose proof (rel_set_in B wb F mv P1 Hr Hlt') as Hr1.
    set (B1 := set_cell B (ofW mv) P1) in *.
    set (wb1 := set_cell wb mv P1) in *.
    assert (Hreply : forall y, is_legal_move B1 y = true ->
      check_win (set_cell B1 y (other_player P1)) (other_player P1) (gen_lines m n k) = false /\
      forces_win (gen_lines m n k) P1 d (set_cell B1 y (other_player P1))).
    { intros y Hy. simpl other_player.
      destruct (inW y) eqn:Hin.
      - (* reply inside the window *)
        pose proof (rel_legal_toW B1 wb1 F y Hr1 Hin Hy) as Hyw.
        assert (Hkey : has_key (toW y) bs = true) by (apply Hcov, in_legal_moves; exact Hyw).
        destruct (has_key_InB _ _ Hkey) as [sub Hsub].
        destruct (wcheck_br_spec bs d wb1 (length F) Hbr (toW y) sub Hsub)
          as [(Heq & _) | (_ & _ & Hd & Hw)].
        + pose proof (toW_lt y Hin). unfold pass_key in Heq. lia.
        + pose proof (rel_set_in B1 wb1 F (toW y) P2 Hr1 (toW_lt y Hin)) as Hr2.
          rewrite ofW_toW in Hr2 by exact Hin.
          split.
          * destruct (check_win (set_cell B1 y P2) P2 (gen_lines m n k)) eqn:Hc; [| reflexivity].
            rewrite (danger_detects _ _ _ Hr2 Hc) in Hd. discriminate.
          * eapply IHbs; eauto.
      - (* reply outside the window: a "far" move *)
        assert (Hkey : has_key pass_key bs = true) by exact Hpass.
        destruct (has_key_InB _ _ Hkey) as [sub Hsub].
        destruct (wcheck_br_spec bs d wb1 (length F) Hbr pass_key sub Hsub)
          as [(_ & Hd & Hw) | (Hneq & _)]; [| contradiction].
        pose proof (rel_set_out B1 wb1 F y Hr1 Hin) as Hr2.
        split.
        + destruct (check_win (set_cell B1 y P2) P2 (gen_lines m n k)) eqn:Hc; [| reflexivity].
          pose proof (danger_detects _ _ _ Hr2 Hc) as Hdd. simpl length in Hdd.
          rewrite Hdd in Hd. discriminate.
        + eapply IHbs; eauto. }
    apply fw_next with (m := ofW mv); [eapply rel_legal_ofW; eauto | | |].
    + apply nonempty_iff in Hne as [c Hc]. apply in_legal_moves in Hc.
      exists (ofW c). eapply rel_legal_ofW; eauto.
    + intros y Hy. apply (Hreply y Hy).
    + intros y Hy. apply (Hreply y Hy).
  - (* BNil *)
    intros c sub [].
  - (* BCons *)
    intros c s Hs rest Hrest c' sub Hin d wb F B Hr Hck.
    destruct Hin as [[-> ->] | Hin].
    + eapply Hs; eauto.
    + eapply Hrest; eauto.
Qed.

(** Main lifting theorem: a window certificate is a forced win on the
    empty m x n board. *)
Theorem window_certificate_lifts : forall ct d,
  wcheck d (empty_board (R * C)) 0 ct = true ->
  forces_win (gen_lines m n k) P1 d (empty_board (m * n)).
Proof.
  intros ct d H. apply (wcheck_sound ct d (empty_board (R * C)) []).
  - apply rel_empty.
  - exact H.
Qed.

End Window.
