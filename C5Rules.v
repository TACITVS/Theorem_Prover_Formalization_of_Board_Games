(** * Follow-up structures and their soundness

    A follow-up structure, attached to a position [b] with the attacker to
    move, partitions the empty cells into
    - STRONG dominoes (lo, hi): vertically adjacent; the defender always
      answers lo with hi, so the defender owns every hi ("claimeven");
    - RIGID pairs (x, y): two cells in different columns whose supporting
      cells are synchronised (both already filled, or themselves a rigid
      pair); the defender answers one with the other ("baseinverse" and
      lock-step chains);
    - WEAK pairs in FREE columns: vertical dominoes or two currently
      playable cells; the defender owns at least one of them ("vertical",
      "baseinverse");
    - the remaining cells of FREE columns, where the defender may spend
      tempo moves;
    - optionally a FROZEN column above a defender THREAT: a cell t that
      would complete a defender line, sitting above an empty cell.  The
      attacker can never fill the cell below t without losing at once.

    If (parity mode) the number of empty free cells is even, the defender
    never has to spend a tempo move outside the free zone.  Without strong
    or rigid units and frozen columns (weak mode) no parity is needed.

    Theorem [structure_sound]: if every winning line already contains a
    defender disc, or a strong upper cell, or a whole pair, or a frozen
    cell above the threat, then the defender cannot lose.  This is
    Allis's zugzwang-control theory for Connect-Four, generalised and
    machine-checked. *)
From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
From C5 Require Import C5Game C5Board C5Principle.

Record structure : Type := mkStruct {
  s_strong : list (cell * cell);
  s_rigid  : list (cell * cell);
  s_weak   : list (cell * cell);
  s_free   : list nat;
  s_frozen : option (nat * nat);   (* (column, row of the threat cell) *)
  s_parity : bool
}.

Definition topc (st : structure) (c : nat) : nat :=
  match s_frozen st with
  | Some (fc, ft) => if c =? fc then ft - 1 else 8
  | None => 8
  end.

Definition all_pairs (st : structure) := s_strong st ++ s_rigid st ++ s_weak st.
Definition unit_cells (st : structure) := pair_cells (all_pairs st).
Definition rigid_cells (st : structure) := pair_cells (s_strong st ++ s_rigid st).

Definition freezone (b : board) (st : structure) : list cell :=
  flat_map (fun c => map (fun r => (c, r))
                         (seq (length (col b c)) (topc st c - length (col b c))))
           (s_free st).

Record Static (d : player) (b : board) (st : structure) : Prop := {
  st_wf : wf b;
  st_frozen : forall fc ft, s_frozen st = Some (fc, ft) ->
     fc < 8 /\ ft < 8 /\ length (col b fc) < ft /\
     exists L, In L lines /\ In (fc, ft) L /\
       forall y, In y L -> y <> (fc, ft) -> owner b y = Some d;
  st_nodup : NoDup (unit_cells st);
  st_cells : forall x, In x (unit_cells st) ->
     fst x < 8 /\ snd x < topc st (fst x) /\ owner b x = None;
  st_strong : forall lo hi, In (lo, hi) (s_strong st) ->
     fst hi = fst lo /\ snd hi = S (snd lo);
  st_rigid : forall x y, In (x, y) (s_rigid st) ->
     fst x <> fst y /\
     ((snd x = length (col b (fst x)) /\ snd y = length (col b (fst y))) \/
      (0 < snd x /\ 0 < snd y /\
       (In ((fst x, snd x - 1), (fst y, snd y - 1)) (s_rigid st) \/
        In ((fst y, snd y - 1), (fst x, snd x - 1)) (s_rigid st))));
  st_rigid_notfree : forall x, In x (rigid_cells st) -> ~ In (fst x) (s_free st);
  st_weak : forall x y, In (x, y) (s_weak st) ->
     In (fst x) (s_free st) /\ In (fst y) (s_free st) /\
     ((fst y = fst x /\ snd y = S (snd x)) \/
      (fst x <> fst y /\ snd x = length (col b (fst x)) /\
       snd y = length (col b (fst y))));
  st_partition : forall c r, c < 8 -> r < 8 -> owner b (c, r) = None ->
     In (c, r) (unit_cells st) \/ (In c (s_free st) /\ r < topc st c) \/
     (exists ft, s_frozen st = Some (c, ft) /\ ft - 1 <= r);
  st_free_nodup : NoDup (s_free st);
  st_free_range : forall c, In c (s_free st) -> c < 8;
  st_mode : if s_parity st
            then Nat.even (count_empty b (freezone b st)) = true
            else s_strong st = [] /\ s_rigid st = [] /\ s_frozen st = None;
  st_cover : forall L, In L lines ->
     (exists y, In y L /\ owner b y = Some d) \/
     (exists lo hi, In (lo, hi) (s_strong st) /\ In hi L) \/
     (exists x y, In (x, y) (all_pairs st) /\ In x L /\ In y L) \/
     (exists fc ft r, s_frozen st = Some (fc, ft) /\ In (fc, r) L /\ ft <= r)
}.

(** The invariant maintained by the follow-up strategy (attacker to move). *)
Record Inv (d : player) (b : board) (st : structure) (b' : board) : Prop := {
  iv_wf : wf b';
  iv_ext : extends b b';
  iv_strong : forall lo hi, In (lo, hi) (s_strong st) ->
     (owner b' lo <> None -> owner b' hi = Some d) /\
     (owner b' hi <> None -> owner b' hi = Some d);
  iv_rigid : forall x y, In (x, y) (s_rigid st) ->
     (owner b' x = None <-> owner b' y = None) /\
     (owner b' x <> None -> owner b' x = Some d \/ owner b' y = Some d);
  iv_weak : forall x y, In (x, y) (s_weak st) ->
     (owner b' x = Some (other d) \/ owner b' y = Some (other d)) ->
     (owner b' x = Some d \/ owner b' y = Some d);
  iv_frozen : forall fc ft, s_frozen st = Some (fc, ft) ->
     length (col b' fc) <= ft - 1;
  iv_parity : s_parity st = true ->
     Nat.even (count_empty b' (freezone b st)) = true
}.

Section Soundness.

Variable d : player.
Variable b : board.
Variable st : structure.
Hypothesis HS : Static d b st.

Let a := other d.

Lemma d_neq_a : d <> a.
Proof. unfold a; intros E; apply (other_neq d); auto. Qed.

Lemma in_all_strong : forall pr, In pr (s_strong st) -> In pr (all_pairs st).
Proof. intros; unfold all_pairs; apply in_app_iff; auto. Qed.
Lemma in_all_rigid : forall pr, In pr (s_rigid st) -> In pr (all_pairs st).
Proof. intros; unfold all_pairs; rewrite !in_app_iff; auto. Qed.
Lemma in_all_weak : forall pr, In pr (s_weak st) -> In pr (all_pairs st).
Proof. intros; unfold all_pairs; rewrite !in_app_iff; auto. Qed.

Lemma unit_cell_of : forall pr z, In pr (all_pairs st) -> (z = fst pr \/ z = snd pr) ->
  In z (unit_cells st).
Proof. intros pr z Hpr Hz. unfold unit_cells. apply in_pair_cells. eauto. Qed.

Lemma same_pair : forall pr pr' z, In pr (all_pairs st) -> In pr' (all_pairs st) ->
  (z = fst pr \/ z = snd pr) -> (z = fst pr' \/ z = snd pr') -> pr = pr'.
Proof. intros. eapply pair_unique; eauto. apply (st_nodup _ _ _ HS). Qed.

Lemma pair_ne : forall pr, In pr (all_pairs st) -> fst pr <> snd pr.
Proof. intros. eapply pair_distinct; eauto. apply (st_nodup _ _ _ HS). Qed.

Lemma static_inv : Inv d b st b.
Proof.
  constructor.
  - exact (st_wf _ _ _ HS).
  - apply extends_refl.
  - intros lo hi Hin.
    assert (Hu : In lo (unit_cells st)) by (eapply unit_cell_of; [apply in_all_strong; eauto|left; auto]).
    assert (Hu' : In hi (unit_cells st)) by (eapply unit_cell_of; [apply in_all_strong; eauto|right; auto]).
    destruct (st_cells _ _ _ HS lo Hu) as [_ [_ Hlo]].
    destruct (st_cells _ _ _ HS hi Hu') as [_ [_ Hhi]].
    split; intros H; [congruence|congruence].
  - intros p q Hin.
    assert (Hu : In p (unit_cells st)) by (eapply unit_cell_of; [apply in_all_rigid; eauto|left; auto]).
    assert (Hu' : In q (unit_cells st)) by (eapply unit_cell_of; [apply in_all_rigid; eauto|right; auto]).
    destruct (st_cells _ _ _ HS p Hu) as [_ [_ Hp]].
    destruct (st_cells _ _ _ HS q Hu') as [_ [_ Hq]].
    split; [split; congruence|intros; congruence].
  - intros p q Hin [H|H].
    + assert (Hu : In p (unit_cells st)) by (eapply unit_cell_of; [apply in_all_weak; eauto|left; auto]).
      destruct (st_cells _ _ _ HS p Hu) as [_ [_ Hp]]. congruence.
    + assert (Hu : In q (unit_cells st)) by (eapply unit_cell_of; [apply in_all_weak; eauto|right; auto]).
      destruct (st_cells _ _ _ HS q Hu) as [_ [_ Hq]]. congruence.
  - intros fc ft Hf.
    destruct (st_frozen _ _ _ HS fc ft Hf) as [_ [_ [Hlt _]]]. lia.
  - intros Hp.
    pose proof (st_mode _ _ _ HS) as Hm. rewrite Hp in Hm. exact Hm.
Qed.

(** The same pair cannot occur in two of the three lists. *)
Lemma strong_not_rigid : forall pr, In pr (s_strong st) -> In pr (s_rigid st) -> False.
Proof.
  intros pr H1 H2. pose proof (st_nodup _ _ _ HS) as Hnd.
  unfold unit_cells, all_pairs in Hnd. rewrite pair_cells_app in Hnd.
  apply (NoDup_app_disjoint _ _ _ (fst pr) Hnd).
  - apply in_pair_cells; eauto.
  - rewrite pair_cells_app; apply in_app_iff; left; apply in_pair_cells; eauto.
Qed.
Lemma strong_not_weak : forall pr, In pr (s_strong st) -> In pr (s_weak st) -> False.
Proof.
  intros pr H1 H2. pose proof (st_nodup _ _ _ HS) as Hnd.
  unfold unit_cells, all_pairs in Hnd. rewrite pair_cells_app in Hnd.
  apply (NoDup_app_disjoint _ _ _ (fst pr) Hnd).
  - apply in_pair_cells; eauto.
  - rewrite pair_cells_app; apply in_app_iff; right; apply in_pair_cells; eauto.
Qed.
Lemma rigid_not_weak : forall pr, In pr (s_rigid st) -> In pr (s_weak st) -> False.
Proof.
  intros pr H1 H2. pose proof (st_nodup _ _ _ HS) as Hnd.
  unfold unit_cells, all_pairs in Hnd. rewrite pair_cells_app in Hnd.
  apply NoDup_app_r in Hnd. rewrite pair_cells_app in Hnd.
  apply (NoDup_app_disjoint _ _ _ (fst pr) Hnd); apply in_pair_cells; eauto.
Qed.

(** ** No attacker line *)
Lemma no_attacker_line : forall b'',
  extends b b'' ->
  (forall lo hi, In (lo, hi) (s_strong st) -> owner b'' hi <> Some a) ->
  (forall x y, In (x, y) (all_pairs st) ->
     ~ (owner b'' x = Some a /\ owner b'' y = Some a)) ->
  (forall fc ft, s_frozen st = Some (fc, ft) -> length (col b'' fc) <= ft) ->
  has_line b'' a = false.
Proof.
  intros b'' Hext Hhi Hpair Hfz.
  apply has_line_false. intros L HL.
  destruct (st_cover _ _ _ HS L HL)
    as [[y [Hy Hd]] | [[lo [hi [Hin Hhin]]] | [[x [y [Hin [Hx Hy]]]] | [fc [ft [r [Hf [Hr Hle]]]]]]]].
  - exists y; split; auto. apply owned_by_false.
    rewrite (Hext y) by congruence. rewrite Hd. intros E; injection E; apply d_neq_a.
  - exists hi; split; auto. apply owned_by_false. eapply Hhi; eauto.
  - destruct (owner b'' x) as [px|] eqn:Ex.
    + destruct (player_dec px a) as [->|Hne].
      * exists y; split; auto. apply owned_by_false. intros Ey.
        apply (Hpair x y Hin); auto.
      * exists x; split; auto. apply owned_by_false. congruence.
    + exists x; split; auto. apply owned_by_false. congruence.
  - exists (fc, r); split; auto. apply owned_by_false.
    assert (owner b'' (fc, r) = None) by (apply owner_None; specialize (Hfz _ _ Hf); lia).
    congruence.
Qed.

(** ** The attacker's move: it never completes a line *)
Section AttackerMove.

Variable b' : board.
Hypothesis HI : Inv d b st b'.
Variable c : nat.
Hypothesis Hc : legal b' c = true.

Let x := landing b' c.
Let b1 := play b' c a.

Lemma Hwf' : wf b'.
Proof. exact (iv_wf _ _ _ _ HI). Qed.

Lemma owner_b1 : forall z, owner b1 z = if cell_eq_dec z x then Some a else owner b' z.
Proof.
  intros z. destruct (cell_eq_dec z x) as [->|Hne].
  - apply owner_play_landing; [exact Hwf'|exact Hc].
  - apply owner_play_other; [exact Hwf'|exact Hc|exact Hne].
Qed.

Lemma x_empty' : owner b' x = None.
Proof. apply landing_empty. Qed.

Lemma x_empty : owner b x = None.
Proof. eapply extends_empty; [exact (iv_ext _ _ _ _ HI)|exact x_empty']. Qed.

Lemma x_range : fst x < 8 /\ snd x < 8.
Proof. apply legal_spec in Hc. unfold x, landing; simpl. lia. Qed.

(** gravity: the cell above an empty cell is empty *)
Lemma above_empty : forall cc r, owner b' (cc, r) = None -> owner b' (cc, S r) = None.
Proof. intros cc r H. apply owner_None in H. apply owner_None. lia. Qed.

Lemma below_filled : forall r, snd x = S r -> owner b' (c, r) <> None.
Proof.
  intros r Hr. unfold x, landing in Hr; simpl in Hr.
  intros E. apply owner_None in E. lia.
Qed.

Lemma x_not_hi : forall lo hi, In (lo, hi) (s_strong st) -> hi <> x.
Proof.
  intros [lc lr] [hc hr] Hin E.
  destruct (st_strong _ _ _ HS _ _ Hin) as [Hc1 Hr1]. simpl in Hc1, Hr1.
  pose proof x_empty' as Hx. unfold x, landing in E, Hx. rewrite <- E in Hx.
  injection E as Ehc Ehr.
  assert (Hlo : owner b' (lc, lr) <> None).
  { intros N. apply owner_None in N. rewrite <- Hc1, Ehc in N. lia. }
  pose proof (proj1 (iv_strong _ _ _ _ HI _ _ Hin) Hlo) as Hd.
  congruence.
Qed.

Lemma attacker_cannot_win : has_line b1 a = false.
Proof.
  apply no_attacker_line.
  - apply extends_play; [exact Hwf'|exact Hc|exact (iv_ext _ _ _ _ HI)].
  - intros lo hi Hin. rewrite owner_b1.
    destruct (cell_eq_dec hi x) as [E|Hne].
    + exfalso; eapply x_not_hi; eauto.
    + intros Eh.
      assert (Hf : owner b' hi <> None) by congruence.
      rewrite (proj2 (iv_strong _ _ _ _ HI _ _ Hin) Hf) in Eh.
      injection Eh; apply d_neq_a.
  - intros p q Hin [Hp Hq].
    rewrite owner_b1 in Hp, Hq.
    pose proof (pair_ne _ Hin) as Hpq. simpl in Hpq.
    unfold all_pairs in Hin. rewrite !in_app_iff in Hin.
    destruct Hin as [Hs|[Hr|Hw]].
    + (* strong *)
      destruct (iv_strong _ _ _ _ HI _ _ Hs) as [H1 H2].
      destruct (st_strong _ _ _ HS _ _ Hs) as [E1 E2].
      destruct (cell_eq_dec p x) as [Hpx|Hpx], (cell_eq_dec q x) as [Hqx|Hqx].
      * apply Hpq; congruence.
      * assert (Hpe : owner b' p = None) by (rewrite Hpx; apply x_empty').
        destruct p as [pc pr], q as [qc qr]; simpl in E1, E2; subst qc qr.
        rewrite (above_empty _ _ Hpe) in Hq. discriminate.
      * eapply x_not_hi; eauto.
      * assert (Hp' : owner b' p <> None) by congruence.
        rewrite (H1 Hp') in Hq. injection Hq; apply d_neq_a.
    + (* rigid *)
      destruct (iv_rigid _ _ _ _ HI _ _ Hr) as [H1 H2].
      destruct (cell_eq_dec p x) as [Hpx|Hpx], (cell_eq_dec q x) as [Hqx|Hqx].
      * apply Hpq; congruence.
      * assert (Hpe : owner b' p = None) by (rewrite Hpx; apply x_empty').
        apply H1 in Hpe. congruence.
      * assert (Hqe : owner b' q = None) by (rewrite Hqx; apply x_empty').
        apply H1 in Hqe. congruence.
      * assert (Hp' : owner b' p <> None) by congruence.
        destruct (H2 Hp') as [E|E]; rewrite E in *;
          [injection Hp|injection Hq]; apply d_neq_a.
    + (* weak *)
      pose proof (iv_weak _ _ _ _ HI _ _ Hw) as H1.
      destruct (cell_eq_dec p x) as [Hpx|Hpx], (cell_eq_dec q x) as [Hqx|Hqx].
      * apply Hpq; congruence.
      * destruct (H1 (or_intror Hq)) as [E|E].
        -- rewrite Hpx, x_empty' in E; discriminate.
        -- rewrite E in Hq; injection Hq; apply d_neq_a.
      * destruct (H1 (or_introl Hp)) as [E|E].
        -- rewrite E in Hp; injection Hp; apply d_neq_a.
        -- rewrite Hqx, x_empty' in E; discriminate.
      * destruct (H1 (or_introl Hp)) as [E|E]; rewrite E in *;
          [injection Hp|injection Hq]; apply d_neq_a.
  - intros fc ft Hf.
    pose proof (iv_frozen _ _ _ _ HI _ _ Hf) as Hle.
    destruct (st_frozen _ _ _ HS _ _ Hf) as [_ [_ [Hlt _]]].
    pose proof Hc as Hc'. apply legal_spec in Hc' as [Hc8 _].
    unfold b1. rewrite col_play by first [exact Hwf' | exact Hc8].
    destruct (fc =? c) eqn:E.
    + apply Nat.eqb_eq in E; subst fc. rewrite length_app; simpl. lia.
    + lia.
Qed.

Lemma Hwf1 : wf b1.
Proof. apply wf_play; [exact Hwf'|exact Hc]. Qed.

Lemma ext1 : extends b b1.
Proof. apply extends_play; [exact Hwf'|exact Hc|exact (iv_ext _ _ _ _ HI)]. Qed.

(** cells strictly below the frozen part *)
Definition low (w : cell) : Prop :=
  forall fc ft, s_frozen st = Some (fc, ft) -> fst w = fc -> snd w < ft - 1.

Lemma low_of_topc : forall w, snd w < topc st (fst w) -> low w.
Proof.
  intros w H fc ft Hf Ew. unfold topc in H. rewrite Hf in H.
  rewrite Ew, Nat.eqb_refl in H. exact H.
Qed.

Lemma low_unit : forall w, In w (unit_cells st) -> low w.
Proof. intros w Hw. apply low_of_topc. apply (st_cells _ _ _ HS w Hw). Qed.

Lemma in_freezone : forall w,
  In w (freezone b st) <->
  In (fst w) (s_free st) /\ length (col b (fst w)) <= snd w /\ snd w < topc st (fst w).
Proof.
  intros [wc wr]; unfold freezone; simpl. rewrite in_flat_map. split.
  - intros [cc [Hcc Hin]]. apply in_map_iff in Hin as [r [E Hr]].
    injection E as <- <-. apply in_seq in Hr. split; [auto|lia].
  - intros [Hf [H1 H2]]. exists wc; split; auto.
    apply in_map_iff. exists wr; split; auto. apply in_seq. lia.
Qed.

Lemma low_free : forall w, In w (freezone b st) -> low w.
Proof. intros w Hw. apply low_of_topc. apply in_freezone in Hw. tauto. Qed.

Lemma freezone_nodup : NoDup (freezone b st).
Proof.
  unfold freezone. pose proof (st_free_nodup _ _ _ HS) as Hnd.
  induction (s_free st) as [|c0 l IH]; simpl; [constructor|].
  inversion Hnd as [|? ? Hnot Hnd']; subst.
  apply NoDup_app.
  - apply NoDup_map_inj; [|apply seq_NoDup].
    intros r1 r2 _ _ E; injection E; auto.
  - apply IH; auto.
  - intros w Hw1 Hw2. apply in_map_iff in Hw1 as [r [<- _]].
    apply in_flat_map in Hw2 as [c1 [Hc1 Hin]].
    apply in_map_iff in Hin as [r' [E _]]. injection E as -> _.
    contradiction.
Qed.

Lemma not_free_of_rigid : forall w, In w (rigid_cells st) -> ~ In w (freezone b st).
Proof.
  intros w Hw Hf. apply in_freezone in Hf as [Hf _].
  exact (st_rigid_notfree _ _ _ HS w Hw Hf).
Qed.

Lemma rigid_cell_of : forall pr z, In pr (s_strong st ++ s_rigid st) ->
  (z = fst pr \/ z = snd pr) -> In z (rigid_cells st).
Proof. intros pr z Hpr Hz. unfold rigid_cells. apply in_pair_cells. eauto. Qed.

Lemma weak_cell_in_free : forall p q w,
  In (p, q) (s_weak st) ->
  (w = p \/ w = q) ->
  In w (freezone b st).
Proof.
  intros p q w Hin Hw. apply in_freezone.
  destruct (st_weak _ _ _ HS _ _ Hin) as [Fp [Fq _]].
  assert (Hu : In w (unit_cells st)).
  { eapply unit_cell_of; [apply in_all_weak; eauto|simpl; tauto]. }
  destruct (st_cells _ _ _ HS w Hu) as [_ [Ht He]].
  apply owner_None in He.
  destruct Hw as [E|E]; subst w; simpl; auto.
Qed.

(** *** The generic reply lemma *)
Section Reply.

Variable c' : nat.
Hypothesis Hc' : legal b1 c' = true.
Let z := landing b1 c'.
Let b2 := play b1 c' d.

Lemma z_empty1 : owner b1 z = None.
Proof. apply landing_empty. Qed.

Lemma z_ne_x : z <> x.
Proof.
  intros E. pose proof z_empty1 as H. rewrite E, owner_b1 in H.
  destruct (cell_eq_dec x x); [discriminate|congruence].
Qed.

Lemma z_empty' : owner b' z = None.
Proof. pose proof z_empty1 as H. rewrite owner_b1 in H.
  destruct (cell_eq_dec z x); [discriminate|exact H]. Qed.

Lemma owner_b2 : forall w,
  owner b2 w = if cell_eq_dec w z then Some d
               else if cell_eq_dec w x then Some a else owner b' w.
Proof.
  intros w. destruct (cell_eq_dec w z) as [->|Hne].
  - apply owner_play_landing; [exact Hwf1|exact Hc'].
  - unfold b2. rewrite owner_play_other by first [exact Hwf1|exact Hc'|exact Hne].
    apply owner_b1.
Qed.

Lemma owner_b2_x : owner b2 x = Some a.
Proof.
  rewrite owner_b2. destruct (cell_eq_dec x z) as [E|_].
  - exfalso; apply z_ne_x; auto.
  - destruct (cell_eq_dec x x); congruence.
Qed.

Lemma owner_b2_z : owner b2 z = Some d.
Proof. rewrite owner_b2. destruct (cell_eq_dec z z); congruence. Qed.

Lemma owner_b2_same : forall w, w <> x -> w <> z -> owner b2 w = owner b' w.
Proof.
  intros w H1 H2. rewrite owner_b2.
  destruct (cell_eq_dec w z); [contradiction|].
  destruct (cell_eq_dec w x); [contradiction|reflexivity].
Qed.

Lemma count_b2 : forall l, NoDup l ->
  ((In x l <-> In z l) ->
   Nat.even (count_empty b' l) = true -> Nat.even (count_empty b2 l) = true).
Proof.
  intros l Hnd Hiff He.
  destruct (count_fill b' b1 x l Hnd x_empty') as [A1 A2].
  { rewrite owner_b1. destruct (cell_eq_dec x x); congruence. }
  { intros w Hw. rewrite owner_b1. destruct (cell_eq_dec w x); [contradiction|reflexivity]. }
  destruct (count_fill b1 b2 z l Hnd z_empty1) as [B1 B2].
  { rewrite owner_b2_z. discriminate. }
  { intros w Hw. unfold b2. apply owner_play_other; [exact Hwf1|exact Hc'|exact Hw]. }
  destruct (in_dec cell_eq_dec x l) as [Hx|Hx].
  - assert (Hz : In z l) by (apply Hiff; auto).
    specialize (A1 Hx). specialize (B1 Hz).
    rewrite <- A1, <- B1 in He. simpl in He. exact He.
  - assert (Hz : ~ In z l) by (intros H; apply Hx, Hiff; auto).
    rewrite (B2 Hz), (A2 Hx); exact He.
Qed.

Lemma reply_inv :
  (forall lo hi, In (lo, hi) (s_strong st) ->
     (lo = x \/ hi = x \/ lo = z \/ hi = z) -> lo = x /\ hi = z) ->
  (forall p q, In (p, q) (s_rigid st) ->
     (p = x \/ q = x \/ p = z \/ q = z) -> (p = x /\ q = z) \/ (p = z /\ q = x)) ->
  (forall p q, In (p, q) (s_weak st) -> (p = x \/ q = x) ->
     p = z \/ q = z \/ owner b' p = Some d \/ owner b' q = Some d) ->
  low x -> low z ->
  (s_parity st = true -> (In x (freezone b st) <-> In z (freezone b st))) ->
  Inv d b st b2.
Proof.
  intros Ca Cb Cc Lx Lz Ce.
  pose proof (iv_strong _ _ _ _ HI) as IS.
  pose proof (iv_rigid _ _ _ _ HI) as IR.
  pose proof (iv_weak _ _ _ _ HI) as IW.
  constructor.
  - apply wf_play; [exact Hwf1|exact Hc'].
  - apply extends_play; [exact Hwf1|exact Hc'|exact ext1].
  - intros lo hi Hin.
    destruct (cell_eq_dec lo x) as [E1|E1];
    [|destruct (cell_eq_dec hi x) as [E2|E2];
      [|destruct (cell_eq_dec lo z) as [E3|E3];
        [|destruct (cell_eq_dec hi z) as [E4|E4]]]];
    try (destruct (Ca lo hi Hin ltac:(tauto)) as [-> ->];
         rewrite owner_b2_z; split; intros; reflexivity).
    rewrite !owner_b2_same by auto. apply IS; auto.
  - intros p q Hin.
    destruct (cell_eq_dec p x) as [E1|E1];
    [|destruct (cell_eq_dec q x) as [E2|E2];
      [|destruct (cell_eq_dec p z) as [E3|E3];
        [|destruct (cell_eq_dec q z) as [E4|E4]]]];
    try (destruct (Cb p q Hin ltac:(tauto)) as [[-> ->]|[-> ->]];
         rewrite owner_b2_x, owner_b2_z;
         [split; [split; discriminate | intros _; right; reflexivity]
         |split; [split; discriminate | intros _; left; reflexivity]]).
    rewrite !owner_b2_same by auto. apply IR; auto.
  - intros p q Hin Hatt.
    pose proof (pair_ne (p, q) (in_all_weak (p, q) Hin)) as Hne. simpl in Hne.
    destruct (cell_eq_dec p z) as [->|E3]; [left; apply owner_b2_z|].
    destruct (cell_eq_dec q z) as [->|E4]; [right; apply owner_b2_z|].
    destruct (cell_eq_dec p x) as [E1|E1]; [|destruct (cell_eq_dec q x) as [E2|E2]].
    + destruct (Cc p q Hin (or_introl E1)) as [->|[->|[H|H]]]; try contradiction.
      * rewrite E1, x_empty' in H; discriminate.
      * right. rewrite owner_b2_same by congruence; auto.
    + destruct (Cc p q Hin (or_intror E2)) as [->|[->|[H|H]]]; try contradiction.
      * left. rewrite owner_b2_same by congruence; auto.
      * rewrite E2, x_empty' in H; discriminate.
    + rewrite !owner_b2_same in * by auto. apply IW; auto.
  - intros fc ft Hf.
    pose proof (iv_frozen _ _ _ _ HI _ _ Hf) as Hle.
    pose proof Hc as Hc0. apply legal_spec in Hc0 as [Hc8 _].
    pose proof Hc' as Hc1. apply legal_spec in Hc1 as [Hc8' _].
    unfold b2, b1.
    rewrite !col_play by first [exact Hwf1|exact Hwf'|exact Hc8'|exact Hc8].
    assert (Hx' : c = fc -> length (col b' c) < ft - 1).
    { intros E. apply (Lx fc ft Hf E). }
    assert (Hz' : c' = fc -> length (col b1 c') < ft - 1).
    { intros E. apply (Lz fc ft Hf E). }
    unfold b1 in Hz'. rewrite col_play in Hz' by first [exact Hwf'|exact Hc8].
    destruct (fc =? c') eqn:E1.
    + apply Nat.eqb_eq in E1. specialize (Hz' (eq_sym E1)).
      rewrite ?length_app; simpl; lia.
    + destruct (fc =? c) eqn:E2.
      * apply Nat.eqb_eq in E2. specialize (Hx' (eq_sym E2)).
        rewrite ?length_app; simpl; lia.
      * exact Hle.
  - intros Hp. apply count_b2; [apply freezone_nodup| |apply (iv_parity _ _ _ _ HI Hp)].
    apply Ce; exact Hp.
Qed.

End Reply.

(** *** Case analysis on the attacker's move *)

Lemma x_in_free_of_weak : forall p q, In (p, q) (s_weak st) -> (x = p \/ x = q) ->
  In x (freezone b st).
Proof.
  intros p q Hin Hx. apply (weak_cell_in_free p q x Hin Hx).
Qed.

Lemma threat_response : forall fc ft,
  s_frozen st = Some (fc, ft) ->
  c = fc ->
  ft - 1 <= snd x ->
  legal b1 fc = true /\ has_line (play b1 fc d) d = true.
Proof.
  intros fc ft Hf Hc_fc Hle_x.
  pose proof (iv_frozen _ _ _ _ HI _ _ Hf) as Hle_b'.
  destruct (st_frozen _ _ _ HS _ _ Hf) as [Hfc [Hft [Hlt [L [HL [HinL Hall]]]]]].
  assert (Hx_snd : snd x = length (col b' fc)) by (unfold x, landing; simpl; subst; auto).
  assert (Hlen_b' : length (col b' fc) = ft - 1) by lia.
  assert (Hcol_b1 : col b1 fc = col b' fc ++ [a]).
  { unfold b1. subst c.
    pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
    rewrite col_play by (exact Hwf' || lia).
    rewrite Nat.eqb_refl. auto. }
  assert (Hlen_b1 : length (col b1 fc) = ft).
  { rewrite Hcol_b1, length_app; simpl. lia. }
  assert (Hleg1 : legal b1 fc = true).
  { apply legal_spec; split; [auto | rewrite Hlen_b1; lia]. }
  split; [exact Hleg1|].
  apply has_line_true with (L := L); [exact HL|].
  intros y Hy.
  destruct (cell_eq_dec y (fc, ft)) as [->|Hne].
  - assert (Hland : landing b1 fc = (fc, ft)) by (unfold landing; rewrite Hlen_b1; auto).
    rewrite <- Hland. apply owner_play_landing; [exact Hwf1|exact Hleg1].
  - assert (Hland : landing b1 fc = (fc, ft)) by (unfold landing; rewrite Hlen_b1; auto).
    assert (Hne_land : y <> landing b1 fc) by congruence.
    rewrite owner_play_other with (x := y) by (exact Hwf1 || exact Hleg1 || exact Hne_land).
    rewrite owner_b1.
    destruct (cell_eq_dec y x) as [->|Hne_x].
    + specialize (Hall x Hy Hne). pose proof x_empty as Hx_e. rewrite Hx_e in Hall. discriminate.
    + rewrite (iv_ext _ _ _ _ HI y).
      * apply Hall; auto.
      * rewrite (Hall y Hy Hne). discriminate.
Qed.

Lemma strong_response : forall lo hi,
  In (lo, hi) (s_strong st) ->
  (x = lo \/ x = hi) ->
  exists c', legal b1 c' = true /\ Inv d b st (play b1 c' d).
Proof.
  intros lo hi Hin [Hx|Hx]; [|exfalso; eapply x_not_hi; eauto].
  pose proof (st_strong _ _ _ HS _ _ Hin) as [Hc_hi Hr_hi].
  pose proof (unit_cell_of (lo, hi) hi (in_all_strong (lo, hi) Hin) (or_intror eq_refl)) as Hu_hi.
  pose proof (unit_cell_of (lo, hi) lo (in_all_strong (lo, hi) Hin) (or_introl eq_refl)) as Hu_lo.
  destruct (st_cells _ _ _ HS hi Hu_hi) as [Hhi_c [Hhi_top Hhi_empty]].
  assert (Hc_lo : c = fst lo) by (rewrite <- Hx; reflexivity).
  assert (Hlen_lo : length (col b' c) = snd lo) by (rewrite <- Hx; reflexivity).
  assert (Hcol_b1 : col b1 c = col b' c ++ [a]).
  { unfold b1.
    pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
    rewrite col_play by (exact Hwf' || lia).
    rewrite Nat.eqb_refl; auto. }
  assert (Hlen_b1 : length (col b1 c) = snd hi).
  { rewrite Hcol_b1, length_app; simpl. rewrite Hlen_lo, Hr_hi. lia. }
  assert (Htop7 : topc st c <= 8).
  { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (c =? fc)|]; try lia.
    destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
  assert (Hleg : legal b1 c = true).
  { apply legal_spec; split.
    - pose proof Hc as Hc_leg; apply legal_spec in Hc_leg; lia.
    - rewrite Hlen_b1. rewrite Hc_hi, <- Hc_lo in Hhi_top. lia. }
  assert (Hz_hi : landing b1 c = hi).
  { unfold landing. rewrite Hlen_b1, Hc_lo, <- Hc_hi. destruct hi; reflexivity. }
  exists c; split; [exact Hleg|].
  apply (reply_inv c Hleg).
  + intros lo' hi' Hin' Htouch.
    assert (Hpair : (lo', hi') = (lo, hi)).
    { destruct Htouch as [H1|[H1|[H1|H1]]].
      - eapply (same_pair (lo', hi') (lo, hi) x); [apply in_all_strong; auto | apply in_all_strong; auto | left; auto | rewrite Hx; left; auto].
      - eapply (same_pair (lo', hi') (lo, hi) x); [apply in_all_strong; auto | apply in_all_strong; auto | right; auto | rewrite Hx; left; auto].
      - eapply (same_pair (lo', hi') (lo, hi) hi); [apply in_all_strong; auto | apply in_all_strong; auto | rewrite <- Hz_hi; left; auto | right; auto].
      - eapply (same_pair (lo', hi') (lo, hi) hi); [apply in_all_strong; auto | apply in_all_strong; auto | rewrite <- Hz_hi; right; auto | right; auto]. }
    injection Hpair as -> ->. rewrite Hz_hi, Hx. auto.
  + intros p q Hin' Htouch. exfalso.
    assert (Hpair : (p, q) = (lo, hi)).
    { destruct Htouch as [H1|[H1|[H1|H1]]].
      - eapply (same_pair (p, q) (lo, hi) x); [apply in_all_rigid; auto | apply in_all_strong; auto | left; auto | rewrite Hx; left; auto].
      - eapply (same_pair (p, q) (lo, hi) x); [apply in_all_rigid; auto | apply in_all_strong; auto | right; auto | rewrite Hx; left; auto].
      - eapply (same_pair (p, q) (lo, hi) hi); [apply in_all_rigid; auto | apply in_all_strong; auto | rewrite <- Hz_hi; left; auto | right; auto].
      - eapply (same_pair (p, q) (lo, hi) hi); [apply in_all_rigid; auto | apply in_all_strong; auto | rewrite <- Hz_hi; right; auto | right; auto]. }
    injection Hpair as -> ->. eapply strong_not_rigid; eauto.
  + intros p q Hin' [H1|H1]; exfalso.
    - assert (Hpair : (p, q) = (lo, hi)).
      { eapply (same_pair (p, q) (lo, hi) x); [apply in_all_weak; auto | apply in_all_strong; auto | left; auto | rewrite Hx; left; auto]. }
      injection Hpair as -> ->. eapply strong_not_weak; eauto.
    - assert (Hpair : (p, q) = (lo, hi)).
      { eapply (same_pair (p, q) (lo, hi) x); [apply in_all_weak; auto | apply in_all_strong; auto | right; auto | rewrite Hx; left; auto]. }
      injection Hpair as -> ->. eapply strong_not_weak; eauto.
  + rewrite Hx. apply low_unit; auto.
  + rewrite Hz_hi. apply low_unit; auto.
  + intros _.
    assert (Hxr : ~ In x (freezone b st)).
    { rewrite Hx. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; left; exact Hin|simpl; auto]. }
    assert (Hzr : ~ In (landing b1 c) (freezone b st)).
    { rewrite Hz_hi. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; left; exact Hin|simpl; auto]. }
    tauto.
Qed.

Lemma rigid_col_sync : forall p q,
  In (p, q) (s_rigid st) ->
  x = p ->
  length (col b' (fst q)) = snd q.
Proof.
  intros p q Hin Hx.
  destruct (st_rigid _ _ _ HS _ _ Hin) as [Hne [Hbase | [Hp0 [Hq0 [Hprev | Hprev]]]]].
  - destruct Hbase as [_ Hq_base].
    assert (Hle1 : length (col b (fst q)) <= length (col b' (fst q))).
    { apply extends_length. exact (iv_ext _ _ _ _ HI). }
    assert (Hqe : owner b' q = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hqe. lia.
  - assert (Hpe_prev : owner b' (fst p, snd p - 1) <> None).
    { intros Hn. apply owner_None in Hn.
      assert (Hlen_p : length (col b' (fst p)) = snd p) by (rewrite <- Hx; reflexivity).
      lia. }
    assert (Hqe_prev : owner b' (fst q, snd q - 1) <> None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hprev)) as Hiff.
      intros Hn. apply Hpe_prev. apply Hiff; exact Hn. }
    assert (Hqe : owner b' q = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hqe.
    destruct (Nat.lt_ge_cases (snd q - 1) (length (col b' (fst q)))) as [Hlt|Hge]; [lia|].
    apply owner_None in Hge. contradiction.
  - assert (Hpe_prev : owner b' (fst p, snd p - 1) <> None).
    { intros Hn. apply owner_None in Hn.
      assert (Hlen_p : length (col b' (fst p)) = snd p) by (rewrite <- Hx; reflexivity).
      lia. }
    assert (Hqe_prev : owner b' (fst q, snd q - 1) <> None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hprev)) as Hiff.
      intros Hn. apply Hpe_prev. apply Hiff; exact Hn. }
    assert (Hqe : owner b' q = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hqe.
    destruct (Nat.lt_ge_cases (snd q - 1) (length (col b' (fst q)))) as [Hlt|Hge]; [lia|].
    apply owner_None in Hge. contradiction.
Qed.

Lemma rigid_col_sync_rev : forall p q,
  In (p, q) (s_rigid st) ->
  x = q ->
  length (col b' (fst p)) = snd p.
Proof.
  intros p q Hin Hx.
  destruct (st_rigid _ _ _ HS _ _ Hin) as [Hne [Hbase | [Hp0 [Hq0 [Hprev | Hprev]]]]].
  - destruct Hbase as [Hp_base _].
    assert (Hle1 : length (col b (fst p)) <= length (col b' (fst p))).
    { apply extends_length. exact (iv_ext _ _ _ _ HI). }
    assert (Hpe : owner b' p = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hpe. lia.
  - assert (Hqe_prev : owner b' (fst q, snd q - 1) <> None).
    { intros Hn. apply owner_None in Hn.
      assert (Hlen_q : length (col b' (fst q)) = snd q) by (rewrite <- Hx; reflexivity).
      lia. }
    assert (Hpe_prev : owner b' (fst p, snd p - 1) <> None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hprev)) as Hiff.
      intros Hn. apply Hqe_prev. apply Hiff; exact Hn. }
    assert (Hpe : owner b' p = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hpe.
    destruct (Nat.lt_ge_cases (snd p - 1) (length (col b' (fst p)))) as [Hlt|Hge]; [lia|].
    apply owner_None in Hge. contradiction.
  - assert (Hqe_prev : owner b' (fst q, snd q - 1) <> None).
    { intros Hn. apply owner_None in Hn.
      assert (Hlen_q : length (col b' (fst q)) = snd q) by (rewrite <- Hx; reflexivity).
      lia. }
    assert (Hpe_prev : owner b' (fst p, snd p - 1) <> None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hprev)) as Hiff.
      intros Hn. apply Hqe_prev. apply Hiff; exact Hn. }
    assert (Hpe : owner b' p = None).
    { pose proof (proj1 (iv_rigid _ _ _ _ HI _ _ Hin)) as Hiff.
      rewrite <- Hx in Hiff. rewrite x_empty' in Hiff. apply Hiff; reflexivity. }
    apply owner_None in Hpe.
    destruct (Nat.lt_ge_cases (snd p - 1) (length (col b' (fst p)))) as [Hlt|Hge]; [lia|].
    apply owner_None in Hge. contradiction.
Qed.

Lemma rigid_response : forall p q,
  In (p, q) (s_rigid st) ->
  (x = p \/ x = q) ->
  exists c', legal b1 c' = true /\ Inv d b st (play b1 c' d).
Proof.
  intros p q Hin [Hx|Hx].
  - pose proof (st_rigid _ _ _ HS _ _ Hin) as [Hne _].
    pose proof (unit_cell_of (p, q) q (in_all_rigid (p, q) Hin) (or_intror eq_refl)) as Hu_q.
    pose proof (unit_cell_of (p, q) p (in_all_rigid (p, q) Hin) (or_introl eq_refl)) as Hu_p.
    destruct (st_cells _ _ _ HS q Hu_q) as [Hq_c [Hq_top Hq_empty]].
    assert (Hc_p : c = fst p) by (rewrite <- Hx; reflexivity).
    assert (Hcol_b1 : col b1 (fst q) = col b' (fst q)).
    { unfold b1.
      pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
      rewrite col_play by (exact Hwf' || lia).
      destruct (fst q =? c) eqn:E; [apply Nat.eqb_eq in E; subst c; exfalso; apply Hne; auto | reflexivity]. }
    assert (Hlen_q : length (col b1 (fst q)) = snd q).
    { rewrite Hcol_b1. apply (rigid_col_sync p q Hin Hx). }
    assert (Htop7 : topc st (fst q) <= 8).
    { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (fst q =? fc)|]; try lia.
      destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
    assert (Hleg : legal b1 (fst q) = true).
    { apply legal_spec; split; [exact Hq_c|rewrite Hlen_q; lia]. }
    assert (Hz_q : landing b1 (fst q) = q).
    { unfold landing. rewrite Hlen_q. destruct q; reflexivity. }
    exists (fst q); split; [exact Hleg|].
    apply (reply_inv (fst q) Hleg).
    + intros lo hi Hin' [H1|[H1|[H1|H1]]]; exfalso;
      [assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; left; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; left; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_rigid; auto | rewrite <- Hz_q; left; auto | right; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_rigid; auto | rewrite <- Hz_q; right; auto | right; auto])];
      injection Hpair as -> ->; eapply strong_not_rigid; eauto.
    + intros p' q' Hin' Htouch.
      assert (Hpair : (p', q') = (p, q)).
      { destruct Htouch as [H1|[H1|[H1|H1]]].
        - eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; left; auto].
        - eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; left; auto].
        - eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_rigid; auto | rewrite <- Hz_q; left; auto | right; auto].
        - eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_rigid; auto | rewrite <- Hz_q; right; auto | right; auto]. }
      injection Hpair as -> ->. rewrite Hz_q, Hx. left; auto.
    + intros p' q' Hin' [H1|H1]; exfalso;
      [assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_weak; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; left; auto])
      |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_weak; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; left; auto])];
      injection Hpair as -> ->; eapply rigid_not_weak; eauto.
    + rewrite Hx. apply low_unit; auto.
    + rewrite Hz_q. apply low_unit; auto.
    + intros _.
      assert (Hxr : ~ In x (freezone b st)).
      { rewrite Hx. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; right; exact Hin|simpl; auto]. }
      assert (Hzr : ~ In (landing b1 (fst q)) (freezone b st)).
      { rewrite Hz_q. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; right; exact Hin|simpl; auto]. }
      tauto.
  - pose proof (st_rigid _ _ _ HS _ _ Hin) as [Hne _].
    pose proof (unit_cell_of (p, q) q (in_all_rigid (p, q) Hin) (or_intror eq_refl)) as Hu_q.
    pose proof (unit_cell_of (p, q) p (in_all_rigid (p, q) Hin) (or_introl eq_refl)) as Hu_p.
    destruct (st_cells _ _ _ HS p Hu_p) as [Hp_c [Hp_top Hp_empty]].
    assert (Hc_q : c = fst q) by (rewrite <- Hx; reflexivity).
    assert (Hcol_b1 : col b1 (fst p) = col b' (fst p)).
    { unfold b1.
      pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
      rewrite col_play by (exact Hwf' || lia).
      destruct (fst p =? c) eqn:E; [apply Nat.eqb_eq in E; subst c; exfalso; apply Hne; auto | reflexivity]. }
    assert (Hlen_p : length (col b1 (fst p)) = snd p).
    { rewrite Hcol_b1. apply (rigid_col_sync_rev p q Hin Hx). }
    assert (Htop7 : topc st (fst p) <= 8).
    { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (fst p =? fc)|]; try lia.
      destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
    assert (Hleg : legal b1 (fst p) = true).
    { apply legal_spec; split; [exact Hp_c|rewrite Hlen_p; lia]. }
    assert (Hz_p : landing b1 (fst p) = p).
    { unfold landing. rewrite Hlen_p. destruct p; reflexivity. }
    exists (fst p); split; [exact Hleg|].
    apply (reply_inv (fst p) Hleg).
    + intros lo hi Hin' [H1|[H1|[H1|H1]]]; exfalso;
      [assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; right; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; right; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) p); [apply in_all_strong; auto | apply in_all_rigid; auto | rewrite <- Hz_p; left; auto | left; auto])
      |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) p); [apply in_all_strong; auto | apply in_all_rigid; auto | rewrite <- Hz_p; right; auto | left; auto])];
      injection Hpair as -> ->; eapply strong_not_rigid; eauto.
    + intros p' q' Hin' Htouch.
      assert (Hpair : (p', q') = (p, q)).
      { destruct Htouch as [H1|[H1|[H1|H1]]].
        - eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; right; auto].
        - eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; right; auto].
        - eapply (same_pair (p', q') (p, q) p); [apply in_all_rigid; auto | apply in_all_rigid; auto | rewrite <- Hz_p; left; auto | left; auto].
        - eapply (same_pair (p', q') (p, q) p); [apply in_all_rigid; auto | apply in_all_rigid; auto | rewrite <- Hz_p; right; auto | left; auto]. }
      injection Hpair as -> ->. rewrite Hz_p, Hx. right; auto.
    + intros p' q' Hin' [H1|H1]; exfalso;
      [assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_weak; auto | apply in_all_rigid; auto | left; auto | rewrite Hx; right; auto])
      |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_weak; auto | apply in_all_rigid; auto | right; auto | rewrite Hx; right; auto])];
      injection Hpair as -> ->; eapply rigid_not_weak; eauto.
    + rewrite Hx. apply low_unit; auto.
    + rewrite Hz_p. apply low_unit; auto.
    + intros _.
      assert (Hxr : ~ In x (freezone b st)).
      { rewrite Hx. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; right; exact Hin|simpl; auto]. }
      assert (Hzr : ~ In (landing b1 (fst p)) (freezone b st)).
      { rewrite Hz_p. apply not_free_of_rigid. eapply rigid_cell_of; [apply in_app_iff; right; exact Hin|simpl; auto]. }
      tauto.
Qed.

Lemma free_move :
  full b1 = false ->
  In x (freezone b st) ->
  ~ In x (rigid_cells st) ->
  (forall p q, In (p, q) (s_weak st) -> (p = x \/ q = x) ->
     owner b' p = Some d \/ owner b' q = Some d) ->
  exists c', legal b1 c' = true /\
    (has_line (play b1 c' d) d = true \/ Inv d b st (play b1 c' d)).
Proof.
  intros Hfull Hxf Hxr Hw.
  pose proof (st_mode _ _ _ HS) as Hmode.
  destruct (s_parity st) eqn:Ep.
  - (* parity mode: answer inside the free zone *)
    pose proof (iv_parity _ _ _ _ HI Ep) as He.
    destruct (count_fill b' b1 x (freezone b st) freezone_nodup x_empty') as [A1 _].
    { rewrite owner_b1. destruct (cell_eq_dec x x); congruence. }
    { intros w Hwx. rewrite owner_b1. destruct (cell_eq_dec w x); [contradiction|reflexivity]. }
    specialize (A1 Hxf).
    assert (Hpos : count_empty b1 (freezone b st) > 0).
    { destruct (count_empty b1 (freezone b st)) eqn:E0; [|lia].
      rewrite <- A1 in He. simpl in He. discriminate. }
    destruct (count_pos _ _ Hpos) as [[wc wr] [Hwin Hwe]].
    pose proof Hwin as Hwin'. apply in_freezone in Hwin' as [Fw [Lw Tw]]. simpl in *.
    apply owner_None in Hwe.
    assert (Hfr := st_free_range _ _ _ HS _ Fw).
    assert (Tw7 : topc st wc <= 8).
    { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (wc =? fc)|]; try lia.
      destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
    assert (Hleg : legal b1 wc = true) by (apply legal_spec; lia).
    exists wc; split; auto. right.
    assert (Hzf : In (landing b1 wc) (freezone b st)).
    { apply in_freezone. unfold landing; simpl. split; auto.
      split; [apply extends_length; exact ext1|lia]. }
    apply (reply_inv wc Hleg).
    + intros lo hi Hin H. exfalso.
      destruct H as [H|[H|[H|H]]].
      * apply Hxr. eapply rigid_cell_of; [apply in_app_iff; left; eauto|simpl; auto].
      * apply Hxr. eapply rigid_cell_of; [apply in_app_iff; left; eauto|simpl; auto].
      * eapply not_free_of_rigid; [|exact Hzf].
        eapply rigid_cell_of; [apply in_app_iff; left; eauto|simpl; auto].
      * eapply not_free_of_rigid; [|exact Hzf].
        eapply rigid_cell_of; [apply in_app_iff; left; eauto|simpl; auto].
    + intros p q Hin H. exfalso.
      destruct H as [H|[H|[H|H]]].
      * apply Hxr. eapply rigid_cell_of; [apply in_app_iff; right; eauto|simpl; auto].
      * apply Hxr. eapply rigid_cell_of; [apply in_app_iff; right; eauto|simpl; auto].
      * eapply not_free_of_rigid; [|exact Hzf].
        eapply rigid_cell_of; [apply in_app_iff; right; eauto|simpl; auto].
      * eapply not_free_of_rigid; [|exact Hzf].
        eapply rigid_cell_of; [apply in_app_iff; right; eauto|simpl; auto].
    + intros p q Hin H. right; right. apply Hw; auto.
    + apply low_free; exact Hxf.
    + apply low_free; exact Hzf.
    + intros _; tauto.
  - (* weak mode: any legal move *)
    destruct Hmode as [Hs [Hr Hf]].
    apply full_false_iff in Hfull as [c' Hc'].
    exists c'; split; auto. right.
    apply (reply_inv c' Hc').
    + intros lo hi Hin. rewrite Hs in Hin; destruct Hin.
    + intros p q Hin. rewrite Hr in Hin; destruct Hin.
    + intros p q Hin H. right; right. apply Hw; auto.
    + intros fc ft E; rewrite Hf in E; discriminate.
    + intros fc ft E; rewrite Hf in E; discriminate.
    + intros E; rewrite Ep in E; discriminate.
Qed.

Lemma weak_response : forall p q,
  In (p, q) (s_weak st) ->
  (x = p \/ x = q) ->
  full b1 = false ->
  exists c', legal b1 c' = true /\
    (has_line (play b1 c' d) d = true \/ Inv d b st (play b1 c' d)).
Proof.
  intros p q Hin Hx Hfull.
  pose proof (unit_cell_of (p, q) p (in_all_weak (p, q) Hin) (or_introl eq_refl)) as Hu_p.
  pose proof (unit_cell_of (p, q) q (in_all_weak (p, q) Hin) (or_intror eq_refl)) as Hu_q.
  destruct (player_dec (match owner b' p with Some d' => if peqb d' d then White else Black | None => Black end) White) as [Hp_d|Hp_notd];
  [|destruct (player_dec (match owner b' q with Some d' => if peqb d' d then White else Black | None => Black end) White) as [Hq_d|Hq_notd]].
  - apply free_move; auto.
    + eapply x_in_free_of_weak; eauto.
    + intros Hrc. destruct (st_weak _ _ _ HS _ _ Hin) as [Fp [Fq _]].
      destruct Hx as [<-|<-]; eapply st_rigid_notfree; eauto.
    + intros p' q' Hin' Htouch.
      assert (Hpair : (p', q') = (p, q)).
      { destruct Htouch as [H1|H1]; destruct Hx as [Hx'|Hx'];
        eapply (same_pair (p', q') (p, q) x);
        try apply in_all_weak; auto; rewrite ?Hx'; auto. }
      injection Hpair as -> ->. left.
      destruct (owner b' p) as [pl|] eqn:Ep; [|discriminate].
      destruct (peqb pl d) eqn:Ed; [apply peqb_eq in Ed; subst; reflexivity|discriminate].
  - apply free_move; auto.
    + eapply x_in_free_of_weak; eauto.
    + intros Hrc. destruct (st_weak _ _ _ HS _ _ Hin) as [Fp [Fq _]].
      destruct Hx as [<-|<-]; eapply st_rigid_notfree; eauto.
    + intros p' q' Hin' Htouch.
      assert (Hpair : (p', q') = (p, q)).
      { destruct Htouch as [H1|H1]; destruct Hx as [Hx'|Hx'];
        eapply (same_pair (p', q') (p, q) x);
        try apply in_all_weak; auto; rewrite ?Hx'; auto. }
      injection Hpair as -> ->. right.
      destruct (owner b' q) as [pl|] eqn:Eq; [|discriminate].
      destruct (peqb pl d) eqn:Ed; [apply peqb_eq in Ed; subst; reflexivity|discriminate].
  - (* Neither p nor q is Some d *)
    assert (Hp_not_d : owner b' p <> Some d).
    { intros Ep. apply Hp_notd. rewrite Ep. destruct d; reflexivity. }
    assert (Hq_not_d : owner b' q <> Some d).
    { intros Eq. apply Hq_notd. rewrite Eq. destruct d; reflexivity. }
    assert (Hpe : owner b' p = None).
    { destruct (owner b' p) as [pl|] eqn:Ep; auto.
      destruct (player_dec pl d) as [->|Hne_d]; [contradiction|].
      assert (pl = a).
      { destruct pl, d; try reflexivity; try contradiction; exfalso; apply Hne_d; reflexivity. }
      subst pl.
      pose proof (iv_weak _ _ _ _ HI _ _ Hin (or_introl Ep)) as [H|H];
      [rewrite Ep in H; contradiction | apply Hq_not_d in H; contradiction]. }
    assert (Hqe : owner b' q = None).
    { destruct (owner b' q) as [pl|] eqn:Eq; auto.
      destruct (player_dec pl d) as [->|Hne_d]; [contradiction|].
      assert (pl = a).
      { destruct pl, d; try reflexivity; try contradiction; exfalso; apply Hne_d; reflexivity. }
      subst pl.
      pose proof (iv_weak _ _ _ _ HI _ _ Hin (or_intror Eq)) as [H|H];
      [apply Hp_not_d in H; contradiction | rewrite Eq in H; contradiction]. }
    destruct (st_weak _ _ _ HS _ _ Hin) as [Fp [Fq [[Hvert_c Hvert_r] | [Hbase_c [Hbase_p Hbase_q]]]]].
    + (* Vertical domino *)
      assert (Hx_p : x = p).
      { destruct Hx as [Hx|Hx]; auto.
        exfalso.
        assert (Hlen : length (col b' (fst q)) = snd q) by (rewrite <- Hx; reflexivity).
        rewrite Hvert_c in Hlen.
        assert (Hlt_p : snd p < length (col b' (fst p))) by (rewrite Hlen, Hvert_r; lia).
        apply owner_None in Hpe. lia. }
      destruct (st_cells _ _ _ HS q Hu_q) as [Hq_c [Hq_top Hq_empty]].
      assert (Hc_p : c = fst p) by (rewrite <- Hx_p; reflexivity).
      assert (Hcol_b1 : col b1 c = col b' c ++ [a]).
      { unfold b1.
        pose proof Hc as Hc_leg; apply legal_spec in Hc_leg as [Hc8 _].
        rewrite col_play by (exact Hwf' || lia).
        rewrite Nat.eqb_refl; auto. }
      assert (Hlen_b1 : length (col b1 c) = snd q).
      { rewrite Hcol_b1, length_app; simpl.
        assert (Hlen_p : length (col b' c) = snd p) by (rewrite <- Hx_p; reflexivity).
        rewrite Hlen_p, Hvert_r. lia. }
      assert (Htop7 : topc st c <= 8).
      { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (c =? fc)|]; try lia.
        destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
      assert (Hleg : legal b1 c = true).
      { apply legal_spec; split.
        - pose proof Hc as Hc_leg; apply legal_spec in Hc_leg; lia.
        - rewrite Hlen_b1.
          assert (Hqc : fst q = c) by (rewrite Hvert_c, <- Hc_p; reflexivity).
          rewrite Hqc in Hq_top. lia. }
      assert (Hz_q : landing b1 c = q).
      { unfold landing. rewrite Hlen_b1, Hc_p, <- Hvert_c. destruct q; reflexivity. }
      exists c; split; [exact Hleg|right].
      apply (reply_inv c Hleg).
      * intros lo hi Hin' [H1|[H1|[H1|H1]]]; exfalso;
        [assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | left; auto | rewrite Hx_p; left; auto])
        |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | right; auto | rewrite Hx_p; left; auto])
        |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_q; left; auto | right; auto])
        |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_q; right; auto | right; auto])];
        injection Hpair as -> ->; eapply strong_not_weak; eauto.
      * intros p' q' Hin' [H1|[H1|[H1|H1]]]; exfalso;
        [assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | left; auto | rewrite Hx_p; left; auto])
        |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | right; auto | rewrite Hx_p; left; auto])
        |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_q; left; auto | right; auto])
        |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_q; right; auto | right; auto])];
        injection Hpair as -> ->; eapply rigid_not_weak; eauto.
      * intros p' q' Hin' Htouch.
        assert (Hpair : (p', q') = (p, q)).
        { destruct Htouch as [H1|H1];
          eapply (same_pair (p', q') (p, q) x);
          try apply in_all_weak; auto; rewrite ?Hx_p; auto. }
        injection Hpair as -> ->. rewrite Hz_q. right; left; auto.
      * rewrite Hx_p. apply low_unit; exact Hu_p.
      * rewrite Hz_q. apply low_unit; exact Hu_q.
      * intros _.
        assert (Hxf : In x (freezone b st)) by (rewrite Hx_p; apply (weak_cell_in_free p q p Hin (or_introl eq_refl))).
        assert (Hzf : In (landing b1 c) (freezone b st)) by (rewrite Hz_q; apply (weak_cell_in_free p q q Hin (or_intror eq_refl))).
        tauto.
    + (* Base pair *)
      destruct Hx as [Hx|Hx].
      * (* x = p, defender plays fst q *)
        destruct (st_cells _ _ _ HS q Hu_q) as [Hq_c [Hq_top Hq_empty]].
        assert (Hc_p : c = fst p) by (rewrite <- Hx; reflexivity).
        assert (Hcol_b1 : col b1 (fst q) = col b' (fst q)).
        { unfold b1.
          pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
          rewrite col_play by (exact Hwf' || lia).
          destruct (fst q =? c) eqn:E; [apply Nat.eqb_eq in E; subst c; exfalso; apply Hbase_c; auto | reflexivity]. }
        assert (Hlen_q : length (col b1 (fst q)) = snd q).
        { rewrite Hcol_b1.
          assert (Hle1 : length (col b (fst q)) <= length (col b' (fst q))) by (apply extends_length; exact (iv_ext _ _ _ _ HI)).
          apply owner_None in Hqe. lia. }
        assert (Htop7 : topc st (fst q) <= 8).
        { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (fst q =? fc)|]; try lia.
          destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
        assert (Hleg : legal b1 (fst q) = true).
        { apply legal_spec; split; [exact Hq_c|rewrite Hlen_q; lia]. }
        assert (Hz_q : landing b1 (fst q) = q).
        { unfold landing. rewrite Hlen_q. destruct q; reflexivity. }
        exists (fst q); split; [exact Hleg|right].
        apply (reply_inv (fst q) Hleg).
        -- intros lo hi Hin' [H1|[H1|[H1|H1]]]; exfalso;
           [assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | left; auto | rewrite Hx; left; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | right; auto | rewrite Hx; left; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_q; left; auto | right; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) q); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_q; right; auto | right; auto])];
           injection Hpair as -> ->; eapply strong_not_weak; eauto.
        -- intros p' q' Hin' [H1|[H1|[H1|H1]]]; exfalso;
           [assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | left; auto | rewrite Hx; left; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | right; auto | rewrite Hx; left; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_q; left; auto | right; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) q); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_q; right; auto | right; auto])];
           injection Hpair as -> ->; eapply rigid_not_weak; eauto.
        -- intros p' q' Hin' Htouch.
           assert (Hpair : (p', q') = (p, q)).
           { destruct Htouch as [H1|H1];
             eapply (same_pair (p', q') (p, q) x);
             try apply in_all_weak; auto; rewrite ?Hx; auto. }
           injection Hpair as -> ->. rewrite Hz_q. right; left; auto.
        -- rewrite Hx. apply low_unit; exact Hu_p.
        -- rewrite Hz_q. apply low_unit; exact Hu_q.
        -- intros _.
           assert (Hxf : In x (freezone b st)) by (rewrite Hx; apply (weak_cell_in_free p q p Hin (or_introl eq_refl))).
           assert (Hzf : In (landing b1 (fst q)) (freezone b st)) by (rewrite Hz_q; apply (weak_cell_in_free p q q Hin (or_intror eq_refl))).
           tauto.
      * (* x = q, defender plays fst p *)
        destruct (st_cells _ _ _ HS p Hu_p) as [Hp_c [Hp_top Hp_empty]].
        assert (Hc_q : c = fst q) by (rewrite <- Hx; reflexivity).
        assert (Hcol_b1 : col b1 (fst p) = col b' (fst p)).
        { unfold b1.
          pose proof Hc as Hc_leg. apply legal_spec in Hc_leg as [Hc8 _].
          rewrite col_play by (exact Hwf' || lia).
          destruct (fst p =? c) eqn:E; [apply Nat.eqb_eq in E; subst c; exfalso; apply Hbase_c; auto | reflexivity]. }
        assert (Hlen_p : length (col b1 (fst p)) = snd p).
        { rewrite Hcol_b1.
          assert (Hle1 : length (col b (fst p)) <= length (col b' (fst p))) by (apply extends_length; exact (iv_ext _ _ _ _ HI)).
          apply owner_None in Hpe. lia. }
        assert (Htop7 : topc st (fst p) <= 8).
        { unfold topc. destruct (s_frozen st) as [[fc ft]|] eqn:Efr; [destruct (fst p =? fc)|]; try lia.
          destruct (st_frozen _ _ _ HS fc ft Efr) as [_ [Hft _]]. lia. }
        assert (Hleg : legal b1 (fst p) = true).
        { apply legal_spec; split; [exact Hp_c|rewrite Hlen_p; lia]. }
        assert (Hz_p : landing b1 (fst p) = p).
        { unfold landing. rewrite Hlen_p. destruct p; reflexivity. }
        exists (fst p); split; [exact Hleg|right].
        apply (reply_inv (fst p) Hleg).
        -- intros lo hi Hin' [H1|[H1|[H1|H1]]]; exfalso;
           [assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | left; auto | rewrite Hx; right; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) x); [apply in_all_strong; auto | apply in_all_weak; auto | right; auto | rewrite Hx; right; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) p); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_p; left; auto | left; auto])
           |assert (Hpair : (lo, hi) = (p, q)) by (eapply (same_pair (lo, hi) (p, q) p); [apply in_all_strong; auto | apply in_all_weak; auto | rewrite <- Hz_p; right; auto | left; auto])];
           injection Hpair as -> ->; eapply strong_not_weak; eauto.
        -- intros p' q' Hin' [H1|[H1|[H1|H1]]]; exfalso;
           [assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | left; auto | rewrite Hx; right; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) x); [apply in_all_rigid; auto | apply in_all_weak; auto | right; auto | rewrite Hx; right; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) p); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_p; left; auto | left; auto])
           |assert (Hpair : (p', q') = (p, q)) by (eapply (same_pair (p', q') (p, q) p); [apply in_all_rigid; auto | apply in_all_weak; auto | rewrite <- Hz_p; right; auto | left; auto])];
           injection Hpair as -> ->; eapply rigid_not_weak; eauto.
        -- intros p' q' Hin' Htouch.
           assert (Hpair : (p', q') = (p, q)).
           { destruct Htouch as [H1|H1];
             eapply (same_pair (p', q') (p, q) x);
             try apply in_all_weak; auto; rewrite ?Hx; auto. }
           injection Hpair as -> ->. rewrite Hz_p. left; auto.
        -- rewrite Hx. apply low_unit; exact Hu_q.
        -- rewrite Hz_p. apply low_unit; exact Hu_p.
        -- intros _.
           assert (Hxf : In x (freezone b st)) by (rewrite Hx; apply (weak_cell_in_free p q q Hin (or_intror eq_refl))).
           assert (Hzf : In (landing b1 (fst p)) (freezone b st)) by (rewrite Hz_p; apply (weak_cell_in_free p q p Hin (or_introl eq_refl))).
           tauto.
Qed.

Lemma attacker_move_safe :
  has_line b1 a = false /\
  (full b1 = true \/
   exists c', legal b1 c' = true /\
     (has_line (play b1 c' d) d = true \/ Inv d b st (play b1 c' d))).
Proof.
  split; [apply attacker_cannot_win|].
  destruct (full b1) eqn:Hfull; [left; reflexivity|right].
  destruct (in_dec cell_eq_dec x (unit_cells st)) as [Hu | Hnot_u].
  - unfold unit_cells in Hu. apply in_pair_cells in Hu as [[p q] [Hin Hx]].
    simpl in Hx.
    unfold all_pairs in Hin. rewrite !in_app_iff in Hin.
    destruct Hin as [Hs | [Hr | Hw]].
    + destruct (strong_response p q Hs Hx) as [c' [Hleg HI2]].
      exists c'; split; [exact Hleg|right; exact HI2].
    + destruct (rigid_response p q Hr Hx) as [c' [Hleg HI2]].
      exists c'; split; [exact Hleg|right; exact HI2].
    + apply (weak_response p q Hw Hx Hfull).
  - assert (Hx_eq : (c, snd x) = x) by (unfold x, landing; reflexivity).
    destruct (st_partition _ _ _ HS c (snd x) (proj1 x_range) (proj2 x_range) x_empty)
      as [Hu | [[Hfree Htop] | [ft [Hfr Hle_ft]]]].
    + exfalso; apply Hnot_u. rewrite <- Hx_eq. exact Hu.
    + apply free_move; auto.
      * apply in_freezone; simpl.
        split; [exact Hfree|split; [apply extends_length; exact (iv_ext _ _ _ _ HI) | exact Htop]].
      * intros Hrc. apply (st_rigid_notfree _ _ _ HS x Hrc Hfree).
      * intros p q Hin Htouch. exfalso. apply Hnot_u.
        eapply unit_cell_of; [apply in_all_weak; eauto|destruct Htouch as [<-|<-]; [left|right]; reflexivity].
    + destruct (threat_response c ft Hfr eq_refl Hle_ft) as [Hleg Hwin].
      exists c; split; [exact Hleg|left; exact Hwin].
Qed.

End AttackerMove.

Theorem structure_sound : safe d b (other d).
Proof.
  apply (follow_up_principle d (Inv d b st)).
  - intros b' Hwf' HI Hfull c Hc.
    apply attacker_move_safe; auto.
  - exact (st_wf _ _ _ HS).
  - apply static_inv.
Qed.

End Soundness.
