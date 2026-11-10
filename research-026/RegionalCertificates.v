(** * Research 026: regional Erdos-Selfridge certificates for the locked game.

    A regional certificate colours every cell with a region id ([reg]) and
    assigns every winning line to a region ([asg]).  The fragment of a line is
    the part of the line inside its assigned region.  With

        weight st l = 0                              if l holds a Black stone,
                    = 2 ^ (5 - |frag l| + #White stones in frag l)   otherwise,

    the certificate condition at a position with White to move is

        for every region r,  sum of weights of the lines assigned to r  <  16.

    This is the Erdos-Selfridge criterion (sum of 2^-|fragment| < 1/2, scaled
    by 32) applied independently on every region.  Pairing strategies are the
    special case of 2-cell regions holding one line each.

    Main results, all against the hash-pinned [trusted/Rules.v]:

    - [regional_certificate_nonloss]: at a valid position with White to move
      that has a regional certificate, the explicit policy
      [regional_policy reg asg] prevents a White win against every total
      White strategy, through the end of the game.

    - [empty_board_has_no_regional_certificate]: no choice of [reg] and [asg]
      is a regional certificate of the empty board.  The proof is a density
      bound: every certified region satisfies 6 * lines <= 5 * cells, while
      6 * 109 > 5 * 125.

    Neither result decides the value of the game. *)

From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Minimax RulesFacts SafePairing Geometry.
From QubicResearch026 Require Import RegionalBarrier.
Import ListNotations.

Local Notation mem c s := (existsb (Nat.eqb c) s).

(** ** 1. Sums over lists *)

Lemma sum_map_add {A} (f g : A -> nat) l :
  list_sum (map (fun x => f x + g x) l) = list_sum (map f l) + list_sum (map g l).
Proof. induction l; simpl; lia. Qed.

Lemma sum_map_le {A} (f g : A -> nat) l :
  (forall x, In x l -> f x <= g x) -> list_sum (map f l) <= list_sum (map g l).
Proof.
  induction l as [|a l IH]; simpl; intros H; [lia|].
  pose proof (H a (or_introl eq_refl)).
  pose proof (IH (fun x Hx => H x (or_intror Hx))). lia.
Qed.

Lemma sum_map_ext_in {A} (f g : A -> nat) l :
  (forall x, In x l -> f x = g x) -> list_sum (map f l) = list_sum (map g l).
Proof. intros H. f_equal. apply map_ext_in. exact H. Qed.

Lemma sum_map_term {A} (f : A -> nat) l x : In x l -> f x <= list_sum (map f l).
Proof.
  induction l as [|a l IH]; simpl; [contradiction|].
  intros [->|H]; [lia|]. specialize (IH H). lia.
Qed.

Lemma sum_map_if {A} (b : bool) (f : A -> nat) l :
  list_sum (map (fun x => if b then f x else 0) l) = if b then list_sum (map f l) else 0.
Proof. destruct b; [reflexivity|]. induction l; simpl; lia. Qed.

Lemma sum_map_filter {A} (p : A -> bool) (f : A -> nat) l :
  list_sum (map (fun x => if p x then f x else 0) l) = list_sum (map f (filter p l)).
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. destruct (p a); simpl; lia. Qed.

Lemma sum_map_const {A} (f : A -> nat) k l :
  (forall x, In x l -> f x = k) -> list_sum (map f l) = length l * k.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH by (intros; apply H; auto). lia.
Qed.

Lemma sum_map_scale_le {A} (f g : A -> nat) a b l :
  (forall x, In x l -> a * f x <= b * g x) ->
  a * list_sum (map f l) <= b * list_sum (map g l).
Proof.
  induction l as [|x l IH]; simpl; intros H; [lia|].
  pose proof (H x (or_introl eq_refl)).
  pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma length_filter_le {A} (p : A -> bool) l : length (filter p l) <= length l.
Proof. induction l as [|a l IH]; simpl; [lia|]. destruct (p a); simpl; lia. Qed.

Lemma sum_indicator (ids : list nat) (v : nat) :
  NoDup ids -> In v ids -> list_sum (map (fun r => if v =? r then 1 else 0) ids) = 1.
Proof.
  induction 1 as [|r ids Hr Hnd IH]; simpl; [contradiction|]. intros [Heq|Hv].
  - subst r. rewrite Nat.eqb_refl. rewrite (sum_map_const _ 0); [lia|].
    intros x Hx. destruct (v =? x) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. subst. contradiction.
  - destruct (v =? r) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|].
    rewrite IH by exact Hv. reflexivity.
Qed.

(** Counting a list by the value of [g] over a duplicate-free list of ids. *)
Lemma partition_count {A} (g : A -> nat) (xs : list A) (ids : list nat) :
  NoDup ids -> (forall x, In x xs -> In (g x) ids) ->
  list_sum (map (fun r => length (filter (fun x => g x =? r) xs)) ids) = length xs.
Proof.
  intros Hnd. induction xs as [|x xs IH]; intros Hin; simpl.
  - rewrite (sum_map_const _ 0 ids); [lia|reflexivity].
  - rewrite (sum_map_ext_in _ (fun r => (if g x =? r then 1 else 0) +
                                       length (filter (fun y => g y =? r) xs))).
    + rewrite sum_map_add, sum_indicator; [|exact Hnd|apply Hin; left; reflexivity].
      rewrite IH by (intros y Hy; apply Hin; right; exact Hy). reflexivity.
    + intros r _. destruct (g x =? r); reflexivity.
Qed.

(** ** 2. Duplicate-free concatenations and ordered pairs *)

Definition disjoint {A} (u v : list A) : Prop := forall z, In z u -> In z v -> False.

Lemma NoDup_concat_disjoint {A} (fs : list (list A)) :
  Forall (@NoDup A) fs -> ForallOrdPairs disjoint fs -> NoDup (concat fs).
Proof.
  intros Hnd Hfop. revert Hnd.
  induction Hfop as [|f fs Hf Hfs IH]; simpl; intros Hnd; [constructor|].
  inversion Hnd as [|? ? Hf0 Hrest]; subst.
  apply NoDup_app; [exact Hf0|apply IH, Hrest|].
  intros z Hz Hz'. apply in_concat in Hz' as [g [Hg Hzg]].
  rewrite Forall_forall in Hf. exact (Hf g Hg z Hz Hzg).
Qed.

Lemma FOP_filter {A} (R : A -> A -> Prop) p l :
  ForallOrdPairs R l -> ForallOrdPairs R (filter p l).
Proof.
  induction 1 as [|a l Ha Hl IH]; simpl; [constructor|].
  destruct (p a); [|exact IH]. constructor; [|exact IH].
  rewrite Forall_forall in *. intros x Hx. apply filter_In in Hx as [Hx _]. apply Ha, Hx.
Qed.

Lemma FOP_map {A B} (R : A -> A -> Prop) (S : B -> B -> Prop) (f : A -> B) l :
  (forall x y, R x y -> S (f x) (f y)) -> ForallOrdPairs R l -> ForallOrdPairs S (map f l).
Proof.
  intros Hf. induction 1 as [|a l Ha Hl IH]; simpl; constructor; [|exact IH].
  rewrite Forall_forall in *. intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
  apply Hf, Ha, Hx.
Qed.

Definition opairs (f : list cell) : list (cell * cell) :=
  concat (map (fun a => map (fun b => (a, b)) (filter (fun b => negb (a =? b)) f)) f).

Lemma opairs_spec f a b : In (a, b) (opairs f) <-> a <> b /\ In a f /\ In b f.
Proof.
  unfold opairs. rewrite in_concat. split.
  - intros [blk [Hblk Hin]]. apply in_map_iff in Hblk as [a' [Heq Ha']]. subst blk.
    apply in_map_iff in Hin as [b' [Heq Hb']]. injection Heq as <- <-.
    apply filter_In in Hb' as [Hb' Hneq]. apply negb_true_iff, Nat.eqb_neq in Hneq.
    split; [exact Hneq|split; assumption].
  - intros [Hneq [Ha Hb]]. eexists. split.
    + apply in_map_iff. exists a. split; [reflexivity|exact Ha].
    + apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb|]. apply negb_true_iff, Nat.eqb_neq. exact Hneq.
Qed.

Lemma filter_neq_length (f : list cell) a :
  NoDup f -> In a f -> length (filter (fun b => negb (a =? b)) f) = length f - 1.
Proof.
  induction 1 as [|h t Hh Ht IH]; [contradiction|]. intros [Heq|Ha].
  - subst h. simpl. rewrite Nat.eqb_refl. simpl.
    assert (Hid : filter (fun b => negb (a =? b)) t = t).
    { apply forallb_filter_id. apply forallb_forall. intros x Hx.
      apply negb_true_iff, Nat.eqb_neq. intros ->. contradiction. }
    rewrite Hid, Nat.sub_0_r. reflexivity.
  - destruct (a =? h) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|].
    simpl. rewrite E. simpl. rewrite IH by exact Ha.
    destruct t; [contradiction|]. simpl. lia.
Qed.

Lemma opairs_length f : NoDup f -> length (opairs f) = length f * (length f - 1).
Proof.
  intros Hnd. unfold opairs. rewrite length_concat, map_map.
  apply sum_map_const. intros a Ha. rewrite length_map.
  apply filter_neq_length; assumption.
Qed.

Lemma opairs_nodup f : NoDup f -> NoDup (opairs f).
Proof.
  intros Hnd. unfold opairs. apply NoDup_concat_disjoint.
  - apply Forall_forall. intros blk Hblk. apply in_map_iff in Hblk as [a [Heq Ha]]. subst blk.
    apply NoDup_map_NoDup_ForallPairs; [|apply NoDup_filter, Hnd].
    intros x y _ _ H. inversion H. reflexivity.
  - assert (Hgen : forall g, NoDup g -> ForallOrdPairs disjoint
      (map (fun a => map (fun b => (a, b)) (filter (fun b => negb (a =? b)) f)) g)).
    { induction 1 as [|a g Ha Hg IH]; simpl; constructor; [|exact IH].
      apply Forall_forall. intros blk Hblk. apply in_map_iff in Hblk as [a' [Heq Ha']].
      subst blk. intros [x y] H1 H2.
      apply in_map_iff in H1 as [b1 [E1 _]]. apply in_map_iff in H2 as [b2 [E2 _]].
      inversion E1; inversion E2; subst. contradiction. }
    apply Hgen, Hnd.
Qed.

(** Two fragments that share at most one cell use disjoint sets of ordered
    pairs, so their pair counts add up to at most the pairs of the region. *)
Definition meet_once (l g : list cell) : Prop :=
  forall a b, a <> b -> In a l -> In b l -> In a g -> In b g -> False.

Lemma pair_packing (frags : list (list cell)) (cells : list cell) :
  NoDup cells -> Forall (@NoDup cell) frags ->
  (forall f c, In f frags -> In c f -> In c cells) ->
  ForallOrdPairs meet_once frags ->
  list_sum (map (fun f => length f * (length f - 1)) frags) <=
    length cells * (length cells - 1).
Proof.
  intros Hc Hnd Hsub Hfop. rewrite <- opairs_length by exact Hc.
  rewrite Forall_forall in Hnd.
  assert (E : list_sum (map (fun f => length f * (length f - 1)) frags) =
              length (concat (map opairs frags))).
  { rewrite length_concat, map_map. apply sum_map_ext_in. intros f Hf.
    rewrite opairs_length; [reflexivity|]. auto. }
  rewrite E. apply NoDup_incl_length.
  - apply NoDup_concat_disjoint.
    + apply Forall_forall. intros p Hp. apply in_map_iff in Hp as [f [Heq Hf]]. subst p.
      apply opairs_nodup. auto.
    + apply (FOP_map meet_once); [|exact Hfop]. intros f g Hfg [a b] H1 H2.
      apply opairs_spec in H1 as [Hab [Ha Hb]]. apply opairs_spec in H2 as [_ [Ha' Hb']].
      exact (Hfg a b Hab Ha Hb Ha' Hb').
  - intros [a b] Hp. apply in_concat in Hp as [p [Hp Hin]].
    apply in_map_iff in Hp as [f [Heq Hf]]. subst p.
    apply opairs_spec in Hin as [Hab [Ha Hb]]. apply opairs_spec. eauto.
Qed.

(** ** 3. Checked facts about the 109 locked lines *)

Fixpoint nodupb (l : list nat) : bool :=
  match l with [] => true | x :: t => negb (mem x t) && nodupb t end.

Lemma nodupb_sound l : nodupb l = true -> NoDup l.
Proof.
  induction l as [|x t IH]; simpl; intros H; [constructor|].
  apply andb_true_iff in H as [Hx Ht]. constructor; [|auto].
  apply negb_true_iff in Hx. intros Hin. apply member_spec in Hin. congruence.
Qed.

Definition common (l g : list cell) : nat := length (filter (fun c => mem c g) l).

Fixpoint meet_onceb (ls : list (list cell)) : bool :=
  match ls with
  | [] => true
  | l :: t => forallb (fun g => common l g <=? 1) t && meet_onceb t
  end.

Lemma line_checks :
  forallb (fun l => nodupb l && (length l =? 5)) all_lines = true /\
  meet_onceb all_lines = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma line_nodup l : In l all_lines -> NoDup l.
Proof.
  intros Hl. destruct line_checks as [H _]. apply forallb_forall with (x := l) in H; [|exact Hl].
  apply andb_true_iff in H as [H _]. apply nodupb_sound, H.
Qed.

Lemma line_length l : In l all_lines -> length l = 5.
Proof.
  intros Hl. destruct line_checks as [H _]. apply forallb_forall with (x := l) in H; [|exact Hl].
  apply andb_true_iff in H as [_ H]. apply Nat.eqb_eq, H.
Qed.

Lemma two_in_length {A} (xs : list A) a b : a <> b -> In a xs -> In b xs -> 2 <= length xs.
Proof.
  intros Hab Ha Hb. destruct xs as [|x [|y t]]; simpl in *; try lia; try contradiction.
  destruct Ha as [Ha|[]]; destruct Hb as [Hb|[]]. congruence.
Qed.

Lemma meet_onceb_sound ls : meet_onceb ls = true -> ForallOrdPairs meet_once ls.
Proof.
  induction ls as [|l t IH]; simpl; intros H; [constructor|].
  apply andb_true_iff in H as [Hl Ht]. constructor; [|auto].
  apply Forall_forall. intros g Hg a b Hab Ha Hb Ha' Hb'.
  apply forallb_forall with (x := g) in Hl; [|exact Hg]. apply Nat.leb_le in Hl.
  unfold common in Hl.
  assert (2 <= length (filter (fun c => mem c g) l)); [|lia].
  apply (two_in_length _ a b Hab); apply filter_In; split; auto; apply member_spec; auto.
Qed.

Lemma lines_meet_once : ForallOrdPairs meet_once all_lines.
Proof. apply meet_onceb_sound. destruct line_checks as [_ H]. exact H. Qed.

(** ** 4. Regional potentials *)

Section Regional.

Variable reg : cell -> nat.
Variable asg : list cell -> nat.

Definition frag (l : list cell) : list cell := filter (fun c => reg c =? asg l) l.

Definition wcount (st : GameState) (l : list cell) : nat :=
  length (filter (fun c => mem c (white_stones st)) (frag l)).

Definition blocked (st : GameState) (l : list cell) : bool :=
  existsb (fun c => mem c (black_stones st)) l.

Definition weight (st : GameState) (l : list cell) : nat :=
  if blocked st l then 0 else 2 ^ (5 - length (frag l) + wcount st l).

(** Scaled potential of region [r]: 32 * sum of 2^-(free cells of fragment). *)
Definition phi (st : GameState) (r : nat) : nat :=
  list_sum (map (fun l => if asg l =? r then weight st l else 0) all_lines).

(** What a White stone on [x] would add to the potential of [reg x]. *)
Definition gain (st : GameState) (x : cell) : nat :=
  list_sum (map (fun l => if mem x (frag l) then weight st l else 0) all_lines).

Definition regional_certificate (st : GameState) : Prop := forall r, phi st r < 16.

Lemma frag_reg l c : In c (frag l) -> reg c = asg l.
Proof. unfold frag. intros H. apply filter_In in H as [_ H]. apply Nat.eqb_eq, H. Qed.

Lemma frag_sub l c : In c (frag l) -> In c l.
Proof. unfold frag. intros H. apply filter_In in H as [H _]. exact H. Qed.

Lemma frag_nodup l : In l all_lines -> NoDup (frag l).
Proof. intros Hl. apply NoDup_filter, line_nodup, Hl. Qed.

Lemma frag_length l : In l all_lines -> length (frag l) <= 5.
Proof. intros Hl. rewrite <- (line_length l Hl). apply length_filter_le. Qed.

(** *** 4a. The empty board has no regional certificate *)

Lemma existsb_nil_false (l : list cell) : existsb (fun c => mem c []) l = false.
Proof. induction l; simpl; auto. Qed.

Lemma filter_nil_mem (l : list cell) : filter (fun c => mem c []) l = [].
Proof. induction l; simpl; auto. Qed.

Lemma phi_initial r :
  phi initial_state r =
  list_sum (map (fun l => 2 ^ (5 - length (frag l))) (filter (fun l => asg l =? r) all_lines)).
Proof.
  unfold phi. rewrite <- sum_map_filter. apply sum_map_ext_in. intros l _.
  unfold weight, blocked, wcount. cbn [white_stones black_stones initial_state].
  rewrite existsb_nil_false, filter_nil_mem. cbn [length]. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma sum_cons {A} (f : A -> nat) a l : list_sum (map f (a :: l)) = f a + list_sum (map f l).
Proof. reflexivity. Qed.

(** A list of fragment sizes, summarised by how many fragments have each size. *)
Lemma size_profile (sz : list nat) :
  Forall (fun s => 2 <= s <= 5) sz ->
  exists x2 x3 x4 x5,
    list_sum (map (fun s => 2 ^ (5 - s)) sz) = 8 * x2 + 4 * x3 + 2 * x4 + x5 /\
    list_sum (map (fun s => s * (s - 1)) sz) = 2 * (x2 + 3 * x3 + 6 * x4 + 10 * x5) /\
    length sz = x2 + x3 + x4 + x5.
Proof.
  induction 1 as [|s sz Hs Hsz IH]; [exists 0, 0, 0, 0; simpl; lia|].
  destruct IH as [x2 [x3 [x4 [x5 [I1 [I2 I3]]]]]].
  rewrite !sum_cons. cbn [length]. rewrite I1, I2, I3.
  assert (Hcase : s = 2 \/ s = 3 \/ s = 4 \/ s = 5) by lia.
  destruct Hcase as [->|[->|[->| ->]]].
  - exists (S x2), x3, x4, x5. simpl. lia.
  - exists x2, (S x3), x4, x5. simpl. lia.
  - exists x2, x3, (S x4), x5. simpl. lia.
  - exists x2, x3, x4, (S x5). simpl. lia.
Qed.

Lemma sizes_bound (sz : list nat) n :
  Forall (fun s => 2 <= s <= 5) sz ->
  list_sum (map (fun s => 2 ^ (5 - s)) sz) <= 15 ->
  list_sum (map (fun s => s * (s - 1)) sz) <= n * (n - 1) ->
  6 * length sz <= 5 * n.
Proof.
  intros Hsz Hb Hp. destruct (size_profile sz Hsz) as [x2 [x3 [x4 [x5 [C1 [C2 C3]]]]]].
  pose proof (region_bound (mk_region x2 x3 x4 x5 n)) as H.
  unfold admissible, fragments in H. cbn [a2 a3 a4 a5 cells] in H.
  rewrite C3. apply H. split; lia.
Qed.

Definition region_cells (r : nat) : list cell := filter (fun c => reg c =? r) all_cells.
Definition region_lines (r : nat) : list (list cell) := filter (fun l => asg l =? r) all_lines.

Lemma region_density r :
  phi initial_state r < 16 ->
  6 * length (region_lines r) <= 5 * length (region_cells r).
Proof.
  intros Hphi. rewrite phi_initial in Hphi. unfold region_lines.
  assert (Hls : forall l, In l (filter (fun l => asg l =? r) all_lines) ->
                          In l all_lines /\ asg l = r).
  { intros l Hl. apply filter_In in Hl as [H1 H2]. apply Nat.eqb_eq in H2. auto. }
  set (ls := filter (fun l => asg l =? r) all_lines) in *.
  replace (length ls) with (length (map (@length cell) (map frag ls)))
    by (rewrite !length_map; reflexivity).
  apply sizes_bound.
  - apply Forall_forall. intros s Hs. rewrite map_map in Hs.
    apply in_map_iff in Hs as [l [Hsl Hl]]. subst s. destruct (Hls l Hl) as [Hall _].
    split; [|apply frag_length, Hall].
    pose proof (sum_map_term (fun l => 2 ^ (5 - length (frag l))) _ l Hl) as Ht.
    cbn beta in Ht.
    destruct (le_lt_dec 2 (length (frag l))) as [Hge|Hlt]; [exact Hge|].
    exfalso. assert (Hcase : length (frag l) = 0 \/ length (frag l) = 1) by lia.
    assert (Hbig : 16 <= 2 ^ (5 - length (frag l)))
      by (destruct Hcase as [E|E]; rewrite E; simpl; lia).
    lia.
  - rewrite !map_map. cbn beta. lia.
  - apply Nat.le_trans with (list_sum (map (fun f => length f * (length f - 1)) (map frag ls)));
      [rewrite !map_map; apply Nat.eq_le_incl; reflexivity|].
    apply pair_packing.
    + apply NoDup_filter, seq_NoDup.
    + apply Forall_forall. intros f Hf. apply in_map_iff in Hf as [l [<- Hl]].
      apply frag_nodup, (Hls l Hl).
    + intros f c Hf Hc. apply in_map_iff in Hf as [l [<- Hl]]. destruct (Hls l Hl) as [Hall Hr].
      unfold region_cells. apply filter_In. split.
      * apply in_seq. pose proof (locked_line_cell_bound l c Hall (frag_sub l c Hc)). lia.
      * apply Nat.eqb_eq. rewrite (frag_reg l c Hc). exact Hr.
    + apply (FOP_map meet_once); [|apply FOP_filter, lines_meet_once].
      intros l g H a b Hab Ha Hb Ha' Hb'.
      exact (H a b Hab (frag_sub _ _ Ha) (frag_sub _ _ Hb) (frag_sub _ _ Ha') (frag_sub _ _ Hb')).
Qed.

Theorem empty_board_density :
  regional_certificate initial_state -> 6 * 109 <= 5 * 125.
Proof.
  intros Hcert.
  set (ids := nodup Nat.eq_dec (map asg all_lines ++ map reg all_cells)).
  assert (Hm : list_sum (map (fun r => length (region_lines r)) ids) = 109).
  { unfold region_lines. rewrite partition_count; [reflexivity|apply NoDup_nodup|].
    intros l Hl. apply nodup_In, in_app_iff. left. apply in_map, Hl. }
  assert (Hn : list_sum (map (fun r => length (region_cells r)) ids) = 125).
  { unfold region_cells. rewrite partition_count; [reflexivity|apply NoDup_nodup|].
    intros c Hc. apply nodup_In, in_app_iff. right. apply in_map, Hc. }
  assert (Hle : 6 * list_sum (map (fun r => length (region_lines r)) ids) <=
                5 * list_sum (map (fun r => length (region_cells r)) ids)).
  { apply sum_map_scale_le. intros r _. apply region_density, Hcert. }
  lia.
Qed.

Theorem empty_board_has_no_regional_certificate : ~ regional_certificate initial_state.
Proof. intros H. pose proof (empty_board_density H). lia. Qed.

(** *** 4b. How one move changes the potentials *)

Definition add_white (st : GameState) (x : cell) : GameState :=
  make_state (x :: white_stones st) (black_stones st) (x :: history st).

Definition add_black (st : GameState) (y : cell) : GameState :=
  make_state (white_stones st) (y :: black_stones st) (y :: history st).

Lemma filter_cons_eq {A} (p : A -> bool) h t :
  filter p (h :: t) = if p h then h :: filter p t else filter p t.
Proof. reflexivity. Qed.

Lemma mem_cons c x W : mem c (x :: W) = (c =? x) || mem c W.
Proof. reflexivity. Qed.

Lemma count_cons_member (f : list cell) x W :
  NoDup f -> ~ In x W ->
  length (filter (fun c => mem c (x :: W)) f) =
  length (filter (fun c => mem c W) f) + (if mem x f then 1 else 0).
Proof.
  intros Hnd Hx. induction Hnd as [|h t Hh Ht IH]; [reflexivity|].
  rewrite !filter_cons_eq. cbn beta. rewrite !mem_cons.
  destruct (Nat.eqb_spec h x) as [->|Hne].
  - assert (Hw : mem x W = false).
    { destruct (mem x W) eqn:E; [apply member_spec in E; contradiction|reflexivity]. }
    assert (Ht' : mem x t = false).
    { destruct (mem x t) eqn:E; [apply member_spec in E; contradiction|reflexivity]. }
    rewrite Ht' in IH. change (if false then 1 else 0) with 0 in IH.
    rewrite Hw, Nat.eqb_refl, Ht'. cbn [orb length]. rewrite IH. lia.
  - assert (E : (x =? h) = false) by (apply Nat.eqb_neq; congruence).
    assert (E' : (h =? x) = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite E. cbn [orb].
    destruct (mem x t); destruct (mem h W); cbn [length]; rewrite IH; lia.
Qed.

Lemma weight_white st x l :
  In l all_lines -> ~ In x (white_stones st) ->
  weight (add_white st x) l = if mem x (frag l) then 2 * weight st l else weight st l.
Proof.
  intros Hl Hx. unfold weight, wcount, blocked. cbn [add_white white_stones black_stones].
  destruct (existsb (fun c => mem c (black_stones st)) l); [destruct (mem x (frag l)); lia|].
  rewrite count_cons_member by (apply frag_nodup, Hl || exact Hx).
  destruct (mem x (frag l)).
  - rewrite Nat.add_assoc, Nat.add_1_r, Nat.pow_succ_r'. reflexivity.
  - rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma phi_white st x r :
  ~ In x (white_stones st) ->
  phi (add_white st x) r = phi st r + (if reg x =? r then gain st x else 0).
Proof.
  intros Hx. unfold phi, gain. rewrite <- sum_map_if, <- sum_map_add.
  apply sum_map_ext_in. intros l Hl. rewrite weight_white by assumption.
  destruct (mem x (frag l)) eqn:Hm.
  - apply member_spec, frag_reg in Hm. rewrite Hm. destruct (asg l =? r); lia.
  - destruct (asg l =? r), (reg x =? r); lia.
Qed.

Lemma gain_white_other st x c :
  ~ In x (white_stones st) -> reg c <> reg x -> gain (add_white st x) c = gain st c.
Proof.
  intros Hx Hreg. unfold gain. apply sum_map_ext_in. intros l Hl.
  rewrite weight_white by assumption.
  destruct (mem c (frag l)) eqn:Hc; [|reflexivity].
  destruct (mem x (frag l)) eqn:Hx'; [|reflexivity].
  apply member_spec, frag_reg in Hc. apply member_spec, frag_reg in Hx'. congruence.
Qed.

Lemma weight_black_le st y l : weight (add_black st y) l <= weight st l.
Proof.
  unfold weight, wcount, blocked. cbn [add_black white_stones black_stones].
  destruct (existsb (fun c => mem c (black_stones st)) l) eqn:Hb.
  - replace (existsb (fun c => mem c (y :: black_stones st)) l) with true; [lia|].
    symmetry. apply existsb_exists in Hb as [c [Hc Hcb]]. apply existsb_exists.
    exists c. split; [exact Hc|]. cbn [existsb]. rewrite Hcb. apply orb_true_r.
  - destruct (existsb (fun c => mem c (y :: black_stones st)) l); lia.
Qed.

Lemma weight_black_zero st y l : In y (frag l) -> weight (add_black st y) l = 0.
Proof.
  intros Hy. unfold weight, blocked. cbn [add_black black_stones].
  replace (existsb (fun c => mem c (y :: black_stones st)) l) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists y. split; [apply frag_sub, Hy|].
  cbn [existsb]. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma phi_black_le st y r : phi (add_black st y) r <= phi st r.
Proof.
  unfold phi. apply sum_map_le. intros l _.
  destruct (asg l =? r); [apply weight_black_le|lia].
Qed.

Lemma gain_black_le st y c : gain (add_black st y) c <= gain st c.
Proof.
  unfold gain. apply sum_map_le. intros l _.
  destruct (mem c (frag l)); [apply weight_black_le|lia].
Qed.

(** Breaker's stone on [y] removes every term that [y] would have doubled. *)
Lemma phi_black_gain st y : phi (add_black st y) (reg y) + gain st y <= phi st (reg y).
Proof.
  unfold phi, gain. rewrite <- sum_map_add. apply sum_map_le. intros l _.
  destruct (mem y (frag l)) eqn:Hy.
  - apply member_spec in Hy. rewrite weight_black_zero by exact Hy.
    rewrite (frag_reg l y Hy), Nat.eqb_refl. lia.
  - pose proof (weight_black_le st y l). destruct (asg l =? reg y); lia.
Qed.

Lemma gain_le_phi st x : gain st x <= phi st (reg x).
Proof.
  unfold gain, phi. apply sum_map_le. intros l _.
  destruct (mem x (frag l)) eqn:H; [|lia].
  apply member_spec, frag_reg in H. rewrite H, Nat.eqb_refl. lia.
Qed.

(** *** 4c. The invariant and the policy *)

(** At a position with White to move: every region is below 32, and no
    White move can push its region to 32. *)
Definition safe (st : GameState) : Prop :=
  (forall r, phi st r < 32) /\
  (forall c, c < 125 -> occupied st c = false -> phi st (reg c) + gain st c < 32).

Lemma certificate_safe st : regional_certificate st -> safe st.
Proof.
  intros H. split.
  - intros r. specialize (H r). lia.
  - intros c _ _. pose proof (gain_le_phi st c). specialize (H (reg c)). lia.
Qed.

Lemma below_32_no_white_win st :
  valid_state st -> (forall r, phi st r < 32) -> has_win (white_stones st) = false.
Proof.
  intros Hvalid Hphi. destruct (has_win (white_stones st)) eqn:Hwin; [|reflexivity].
  exfalso. unfold has_win in Hwin. apply existsb_exists in Hwin as [l [Hl Hline]].
  assert (Hall : forall c, In c l -> In c (white_stones st)).
  { intros c Hc. unfold has_line in Hline.
    apply forallb_forall with (x := c) in Hline; [apply member_spec, Hline|exact Hc]. }
  assert (Hw : weight st l = 32).
  { unfold weight, blocked, wcount.
    replace (existsb (fun c => mem c (black_stones st)) l) with false.
    - rewrite forallb_filter_id.
      + pose proof (frag_length l Hl). rewrite Nat.sub_add by exact H. reflexivity.
      + apply forallb_forall. intros c Hc. apply member_spec, Hall, frag_sub, Hc.
    - symmetry. apply not_true_iff_false. intros Hb.
      apply existsb_exists in Hb as [c [Hc Hcb]]. apply member_spec in Hcb.
      exact (valid_colors_disjoint st c Hvalid (Hall c Hc) Hcb). }
  pose proof (sum_map_term (fun g => if asg g =? asg l then weight st g else 0) all_lines l Hl)
    as Ht.
  cbn beta in Ht. rewrite Nat.eqb_refl, Hw in Ht. specialize (Hphi (asg l)). unfold phi in Hphi. lia.
Qed.

Fixpoint best (f : cell -> nat) (l : list cell) : option cell :=
  match l with
  | [] => None
  | c :: t =>
    match best f t with
    | None => Some c
    | Some b => if f c <? f b then Some b else Some c
    end
  end.

Lemma best_spec f l y : best f l = Some y -> In y l /\ forall c, In c l -> f c <= f y.
Proof.
  revert y. induction l as [|c t IH]; simpl; intros y H; [discriminate|].
  destruct (best f t) as [b|] eqn:E.
  - destruct (IH b eq_refl) as [Hb Hmax].
    destruct (f c <? f b) eqn:Hlt; inversion H; subst y.
    + apply Nat.ltb_lt in Hlt. split; [auto|]. intros d [<-|Hd]; [lia|auto].
    + apply Nat.ltb_ge in Hlt. split; [auto|]. intros d [<-|Hd]; [lia|].
      specialize (Hmax d Hd). lia.
  - inversion H; subst y. split; [auto|]. intros d [<-|Hd]; [lia|].
    destruct t as [|e t']; [contradiction|]. simpl in E.
    destruct (best f t'); [destruct (f e <? f _); discriminate|discriminate].
Qed.

Lemma best_some f l c : In c l -> exists y, best f l = Some y.
Proof.
  destruct l as [|d t]; [contradiction|]. intros _. simpl.
  destruct (best f t); [destruct (f d <? f c0); eauto|eauto].
Qed.

Definition candidates_in (cs : list cell) (st : GameState) (x : cell) : list cell :=
  filter (fun c => (reg c =? reg x) && negb (occupied st c)) cs.

Definition candidates (st : GameState) (x : cell) : list cell := candidates_in all_cells st x.

(** Breaker answers inside the region of White's last move, on the free cell
    that White would gain most from. Otherwise any reply is acceptable. *)
Definition regional_policy : BlackStrategy :=
  fun st => match history st with
  | [] => 0
  | x :: _ => match best (gain st) (candidates st x) with Some y => y | None => 0 end
  end.

Lemma occupied_add_white st x c :
  occupied (add_white st x) c = false -> c <> x /\ occupied st c = false.
Proof.
  intros H. unfold occupied in *. cbn [add_white white_stones black_stones existsb] in H.
  apply orb_false_iff in H as [H1 H2]. apply orb_false_iff in H1 as [H0 H1].
  apply Nat.eqb_neq in H0. split; [exact H0|]. rewrite H1, H2. reflexivity.
Qed.

Lemma occupied_add_black st y c :
  occupied (add_black st y) c = false -> c <> y /\ occupied st c = false.
Proof.
  intros H. unfold occupied in *. cbn [add_black white_stones black_stones existsb] in H.
  apply orb_false_iff in H as [H1 H2]. apply orb_false_iff in H2 as [H0 H2].
  apply Nat.eqb_neq in H0. split; [exact H0|]. rewrite H1, H2. reflexivity.
Qed.

Lemma white_move_safe st request :
  valid_state st -> length (history st) < 125 -> safe st ->
  let x := effective_move st request in
  ~ In x (white_stones st) /\ forall r, phi (move_state true st request) r < 32.
Proof.
  intros Hvalid Hlen [Hphi Hgain]. cbv zeta.
  pose proof (effective_move_is_legal st request Hvalid Hlen) as Hlegal.
  destruct (legal_move_fresh st _ Hlegal) as [Hbound [Hw Hb]].
  split; [exact Hw|]. intros r.
  change (move_state true st request) with (add_white st (effective_move st request)).
  rewrite phi_white by exact Hw.
  destruct (reg (effective_move st request) =? r) eqn:E; [|rewrite Nat.add_0_r; apply Hphi].
  apply Nat.eqb_eq in E. subst r. apply Hgain; [exact Hbound|].
  unfold is_legal_move in Hlegal. apply andb_true_iff in Hlegal as [_ Hfree].
  apply negb_true_iff, Hfree.
Qed.

Lemma reply_core st x y :
  ~ In x (white_stones st) -> safe st -> (forall r, phi (add_white st x) r < 32) ->
  (forall c, c < 125 -> occupied (add_white st x) c = false -> reg c = reg x ->
     reg y = reg x /\ gain (add_white st x) c <= gain (add_white st x) y) ->
  safe (add_black (add_white st x) y).
Proof.
  intros Hxw [Hphi Hgain] Hphi1 Hchoice. split.
  - intros r. pose proof (phi_black_le (add_white st x) y r). specialize (Hphi1 r). lia.
  - intros c Hc Hfree.
    destruct (occupied_add_black _ y c Hfree) as [Hcy Hfree1].
    destruct (occupied_add_white st x c Hfree1) as [Hcx Hfree0].
    pose proof (gain_black_le (add_white st x) y c) as Hg2.
    destruct (Nat.eq_dec (reg c) (reg x)) as [Hrc|Hrc].
    + destruct (Hchoice c Hc Hfree1 Hrc) as [Hry Hmax].
      pose proof (phi_black_gain (add_white st x) y) as Hpg. rewrite Hry, <- Hrc in Hpg.
      specialize (Hphi1 (reg c)). lia.
    + pose proof (phi_black_le (add_white st x) y (reg c)) as Hp2.
      assert (Hp1 : phi (add_white st x) (reg c) = phi st (reg c)).
      { rewrite phi_white by exact Hxw.
        destruct (reg x =? reg c) eqn:E; [apply Nat.eqb_eq in E; congruence|lia]. }
      assert (Hg1 : gain (add_white st x) c = gain st c) by (apply gain_white_other; assumption).
      specialize (Hgain c Hc Hfree0). lia.
Qed.

Lemma all_cells_spec z : In z all_cells <-> z < 125.
Proof. unfold all_cells. rewrite in_seq. lia. Qed.

Lemma candidates_in_intro cs st x c :
  In c cs -> occupied st c = false -> reg c = reg x -> In c (candidates_in cs st x).
Proof.
  intros Hc Hfree Hrc. unfold candidates_in. apply filter_In. split; [exact Hc|].
  rewrite Hrc, Nat.eqb_refl, Hfree. reflexivity.
Qed.

Lemma candidates_in_elim cs st x y :
  (forall z, In z cs -> z < 125) -> In y (candidates_in cs st x) ->
  is_legal_move st y = true /\ reg y = reg x.
Proof.
  intros Hcs Hy. unfold candidates_in in Hy. apply filter_In in Hy as [Hy Hy'].
  apply andb_true_iff in Hy' as [Hry Hfy]. apply Nat.eqb_eq in Hry. split; [|exact Hry].
  unfold is_legal_move. apply andb_true_iff. split; [|exact Hfy].
  apply Nat.ltb_lt. apply Hcs, Hy.
Qed.

Lemma candidates_intro st x c :
  c < 125 -> occupied st c = false -> reg c = reg x -> In c (candidates st x).
Proof.
  intros Hc Hfree Hrc. apply candidates_in_intro; [apply all_cells_spec, Hc|exact Hfree|exact Hrc].
Qed.

Lemma candidates_elim st x y :
  In y (candidates st x) -> is_legal_move st y = true /\ reg y = reg x.
Proof. apply candidates_in_elim. intros z Hz. apply all_cells_spec, Hz. Qed.
Lemma policy_after_white st x :
  regional_policy (add_white st x) =
  match best (gain (add_white st x)) (candidates (add_white st x) x) with
  | Some y => y | None => 0 end.
Proof. reflexivity. Qed.

Lemma effective_legal st y : is_legal_move st y = true -> effective_move st y = y.
Proof. intros H. unfold effective_move. rewrite H. reflexivity. Qed.

Lemma policy_choice st x c :
  c < 125 -> occupied (add_white st x) c = false -> reg c = reg x ->
  reg (effective_move (add_white st x) (regional_policy (add_white st x))) = reg x /\
  gain (add_white st x) c <=
    gain (add_white st x) (effective_move (add_white st x) (regional_policy (add_white st x))).
Proof.
  intros Hc Hfree Hrc.
  pose proof (candidates_intro (add_white st x) x c Hc Hfree Hrc) as Hcand.
  destruct (best_some (gain (add_white st x)) _ c Hcand) as [y0 Hbest].
  destruct (best_spec _ _ _ Hbest) as [Hy0 Hmax].
  destruct (candidates_elim _ _ _ Hy0) as [Hlegal Hry].
  rewrite policy_after_white, Hbest, (effective_legal _ _ Hlegal).
  split; [exact Hry|apply Hmax, Hcand].
Qed.

Lemma regional_reply_restores st request :
  valid_state st -> length (history st) < 125 -> safe st ->
  let st1 := move_state true st request in
  safe (move_state false st1 (regional_policy st1)).
Proof.
  intros Hvalid Hlen Hsafe. cbv zeta.
  destruct (white_move_safe st request Hvalid Hlen Hsafe) as [Hxw Hphi1]. cbv zeta in Hxw.
  change (move_state true st request) with (add_white st (effective_move st request)) in *.
  remember (effective_move st request) as x eqn:Hx. clear Hx.
  change (safe (add_black (add_white st x)
    (effective_move (add_white st x) (regional_policy (add_white st x))))).
  apply reply_core; [exact Hxw|exact Hsafe|exact Hphi1|].
  intros c Hc Hfree Hrc. apply policy_choice; assumption.
Qed.

(** *** 4d. Soundness against the locked evaluator *)

Theorem regional_policy_nonloss : forall n st w,
  n + length (history st) = 125 -> valid_state st -> safe st ->
  outcome (step_game n true st w regional_policy) <> WhiteWins.
Proof.
  fix IH 1. intros n st w Hlen Hvalid Hsafe.
  destruct n as [|n]; [discriminate|].
  rewrite step_game_equation. cbn zeta.
  set (after_white := move_state true st (w st)).
  assert (Hwhite_len : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  assert (Hwhite_valid : valid_state after_white) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  assert (Hno_win : has_win (white_stones after_white) = false).
  { apply below_32_no_white_win; [exact Hwhite_valid|].
    apply (white_move_safe st (w st)); [exact Hvalid|lia|exact Hsafe]. }
  unfold move_result at 1. rewrite Hno_win.
  destruct (length (history after_white) =? 125) eqn:Hfull; [discriminate|].
  apply Nat.eqb_neq in Hfull.
  destruct n as [|n]; [exfalso; apply Hfull; lia|].
  rewrite step_game_equation. cbn zeta.
  change (outcome
    (let next := move_state false after_white (regional_policy after_white) in
     match move_result false next with
     | Some r => make_trace next r
     | None => step_game n true next w regional_policy
     end) <> WhiteWins).
  set (after_black := move_state false after_white (regional_policy after_white)).
  cbv zeta.
  assert (Hblack_len : length (history after_black) = S (length (history after_white)))
    by (apply move_state_history).
  assert (Hblack_valid : valid_state after_black) by
    (apply move_preserves_validity; [exact Hwhite_valid|lia]).
  assert (Hblack_safe : safe after_black).
  { apply (regional_reply_restores st (w st)); [exact Hvalid|lia|exact Hsafe]. }
  unfold move_result.
  destruct (has_win (black_stones after_black)); [discriminate|].
  destruct (length (history after_black) =? 125); [discriminate|].
  apply (IH n after_black w); try assumption. lia.
Qed.

Theorem regional_certificate_nonloss : forall n st w,
  n + length (history st) = 125 -> valid_state st -> regional_certificate st ->
  outcome (step_game n true st w regional_policy) <> WhiteWins.
Proof.
  intros n st w Hlen Hvalid Hcert.
  apply regional_policy_nonloss; [exact Hlen|exact Hvalid|apply certificate_safe, Hcert].
Qed.

End Regional.

(** ** 5. Executable certificate check *)

Definition regional_certificateb (reg : cell -> nat) (asg : list cell -> nat)
    (st : GameState) : bool :=
  forallb (fun r => phi reg asg st r <? 16) (map asg all_lines).

Lemma phi_unused reg asg st r :
  ~ In r (map asg all_lines) -> phi reg asg st r = 0.
Proof.
  intros Hr. unfold phi. apply (sum_map_const _ 0). intros l Hl.
  destruct (asg l =? r) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. exfalso. apply Hr. rewrite <- E. apply in_map, Hl.
Qed.

Theorem regional_certificateb_sound reg asg st :
  regional_certificateb reg asg st = true -> regional_certificate reg asg st.
Proof.
  intros H r. destruct (in_dec Nat.eq_dec r (map asg all_lines)) as [Hr|Hr].
  - unfold regional_certificateb in H. apply forallb_forall with (x := r) in H; [|exact Hr].
    apply Nat.ltb_lt, H.
  - rewrite phi_unused by exact Hr. lia.
Qed.

Theorem checked_regional_leaf_policy : forall reg asg st n w,
  regional_certificateb reg asg st = true -> valid_state st ->
  n + length (history st) = 125 ->
  outcome (step_game n true st w (regional_policy reg asg)) <> WhiteWins.
Proof.
  intros reg asg st n w H Hvalid Hlen.
  apply regional_certificate_nonloss; [exact Hlen|exact Hvalid|].
  apply regional_certificateb_sound, H.
Qed.

(** ** 6. Every pairing leaf is a regional certificate

    A pair {c, mate c} becomes a region; each covered line is assigned to the
    region of one of its pairs.  Its fragment is exactly that pair, so its
    weight is 2^(5-2) = 8, and two lines never share a pair.  Hence every
    region has potential at most 8 < 16.  Combined with Section 4a this
    re-derives, as a special case, that no static pairing certifies the empty
    board. *)

Definition pair_region (mate : mate_function) (c : cell) : nat := Nat.min c (mate c).

Definition line_region (mate : mate_function) (l : list cell) : nat :=
  match find (fun c => negb (mate c =? c) && mem (mate c) l) l with
  | Some c => pair_region mate c
  | None => 0
  end.

Lemma pair_region_cases mate c d :
  well_mated mate -> c < 125 -> d < 125 ->
  pair_region mate d = pair_region mate c -> d = c \/ d = mate c.
Proof.
  intros Hm Hc Hd E. unfold pair_region in E.
  destruct (Hm c Hc) as [_ Hcc]. destruct (Hm d Hd) as [_ Hdd].
  destruct (Nat.min_spec c (mate c)) as [[_ Ec]|[_ Ec]];
  destruct (Nat.min_spec d (mate d)) as [[_ Ed]|[_ Ed]]; rewrite Ec, Ed in E.
  - left. exact E.
  - right. rewrite <- E, Hdd. reflexivity.
  - right. exact E.
  - left. rewrite <- Hdd, E, Hcc. reflexivity.
Qed.

Lemma sum_at_most_one {A} (f : A -> nat) (L : list A) k :
  NoDup L -> (forall x, In x L -> f x <= k) ->
  (forall x y, In x L -> In y L -> 0 < f x -> 0 < f y -> x = y) ->
  list_sum (map f L) <= k.
Proof.
  induction 1 as [|a L Ha Hnd IH]; simpl; intros Hk Huniq; [lia|].
  destruct (Nat.eq_dec (f a) 0) as [E|E].
  - rewrite E. apply IH.
    + intros x Hx. apply Hk. right. exact Hx.
    + intros x y Hx Hy. apply Huniq; right; assumption.
  - rewrite (sum_map_const f 0 L).
    + pose proof (Hk a (or_introl eq_refl)). lia.
    + intros x Hx. destruct (Nat.eq_dec (f x) 0) as [Ex|Ex]; [exact Ex|].
      exfalso. assert (a = x) by (apply Huniq; [left; reflexivity|right; exact Hx|lia|lia]).
      subst. contradiction.
Qed.

Lemma blocked_intro st l c :
  In c l -> In c (black_stones st) -> blocked st l = true.
Proof.
  intros Hc Hb. unfold blocked. apply existsb_exists. exists c.
  split; [exact Hc|apply member_spec, Hb].
Qed.

Lemma length_two (f : list cell) a b :
  NoDup f -> a <> b -> In a f -> In b f -> (forall d, In d f -> d = a \/ d = b) ->
  length f = 2.
Proof.
  intros Hnd Hab Ha Hb Hall.
  pose proof (two_in_length f a b Hab Ha Hb).
  assert (length f <= length [a; b]).
  { apply NoDup_incl_length; [exact Hnd|]. intros d Hd.
    destruct (Hall d Hd) as [->| ->]; simpl; auto. }
  simpl in *. lia.
Qed.

Lemma paired_line_shape mate st l :
  well_mated mate -> pairing_safe mate st -> In l all_lines ->
  0 < weight (pair_region mate) (line_region mate) st l ->
  exists c0, In c0 l /\ In (mate c0) l /\ mate c0 <> c0 /\
    line_region mate l = pair_region mate c0 /\
    weight (pair_region mate) (line_region mate) st l = 8.
Proof.
  intros Hm [Hresp Hcov] Hl Hpos.
  set (reg := pair_region mate) in *. set (asg := line_region mate) in *.
  destruct (blocked st l) eqn:Hb.
  { unfold weight in Hpos. rewrite Hb in Hpos. lia. }
  assert (Hnotblack : forall c, In c l -> ~ In c (black_stones st)).
  { intros c Hc Hcb. rewrite (blocked_intro st l c Hc Hcb) in Hb. discriminate. }
  destruct (find (fun c => negb (mate c =? c) && mem (mate c) l) l) as [c0|] eqn:Hf.
  2:{ exfalso. destruct (Hcov l Hl) as [[c [Hc Hcb]]|[c [Hc [Hd Hne]]]];
      [exact (Hnotblack c Hc Hcb)|].
      pose proof (find_none _ _ Hf c Hc) as H. cbn beta in H.
      apply andb_false_iff in H as [H|H].
      - apply negb_false_iff, Nat.eqb_eq in H. contradiction.
      - assert (Hyes : mem (mate c) l = true) by (apply member_spec, Hd). congruence. }
  pose proof (find_some _ _ Hf) as [Hc0 Hp]. apply andb_true_iff in Hp as [Hne Hd0].
  apply negb_true_iff, Nat.eqb_neq in Hne. apply member_spec in Hd0.
  assert (Hasg : asg l = reg c0) by (unfold asg, line_region; rewrite Hf; reflexivity).
  exists c0. split; [exact Hc0|]. split; [exact Hd0|]. split; [exact Hne|].
  split; [exact Hasg|].
  assert (Hb0 : c0 < 125) by (eapply locked_line_cell_bound; eassumption).
  destruct (Hm c0 Hb0) as [Hb1 Hinv].
  assert (Hpair : forall d, In d (frag reg asg l) -> d = c0 \/ d = mate c0).
  { intros d Hd. pose proof (frag_reg reg asg l d Hd) as Hr. rewrite Hasg in Hr.
    apply (pair_region_cases mate c0 d Hm Hb0); [|exact Hr].
    eapply locked_line_cell_bound; [exact Hl|apply (frag_sub reg asg l d Hd)]. }
  assert (Hin : forall d, In d l -> reg d = reg c0 -> In d (frag reg asg l)).
  { intros d Hd Hr. unfold frag. apply filter_In. split; [exact Hd|].
    rewrite Hasg, Hr. apply Nat.eqb_refl. }
  assert (Hlen : length (frag reg asg l) = 2).
  { apply (length_two _ c0 (mate c0)); [apply frag_nodup, Hl|congruence| | |exact Hpair].
    - apply Hin; [exact Hc0|reflexivity].
    - apply Hin; [exact Hd0|]. unfold reg, pair_region. rewrite Hinv. apply Nat.min_comm. }
  assert (Hw : wcount reg asg st l = 0).
  { unfold wcount. destruct (filter _ _) as [|d rest] eqn:E; [reflexivity|exfalso].
    assert (Hd : In d (filter (fun c => mem c (white_stones st)) (frag reg asg l)))
      by (rewrite E; left; reflexivity).
    apply filter_In in Hd as [Hd Hw]. apply member_spec in Hw.
    destruct (Hpair d Hd) as [->| ->].
    - exact (Hnotblack (mate c0) Hd0 (Hresp c0 Hb0 Hne Hw)).
    - assert (Hne' : mate (mate c0) <> mate c0) by (rewrite Hinv; congruence).
      pose proof (Hresp (mate c0) Hb1 Hne' Hw) as H. rewrite Hinv in H.
      exact (Hnotblack c0 Hc0 H). }
  unfold weight. rewrite Hb, Hlen, Hw. reflexivity.
Qed.

Theorem pairing_leaf_is_regional mate st :
  well_mated mate -> pairing_safe mate st ->
  regional_certificate (pair_region mate) (line_region mate) st.
Proof.
  intros Hm Hsafe r. unfold phi. apply Nat.le_lt_trans with 8; [|lia].
  apply sum_at_most_one; [exact locked_lines_distinct| |].
  - intros l Hl. destruct (line_region mate l =? r); [|lia].
    destruct (Nat.eq_dec (weight (pair_region mate) (line_region mate) st l) 0) as [E|E]; [lia|].
    destruct (paired_line_shape mate st l Hm Hsafe Hl ltac:(lia)) as [? [_ [_ [_ [_ H]]]]]. lia.
  - intros l1 l2 Hl1 Hl2 H1 H2.
    destruct (line_region mate l1 =? r) eqn:E1; [|lia].
    destruct (line_region mate l2 =? r) eqn:E2; [|lia].
    apply Nat.eqb_eq in E1, E2.
    destruct (paired_line_shape mate st l1 Hm Hsafe Hl1 H1) as [c1 [Hc1 [Hd1 [Hne1 [R1 _]]]]].
    destruct (paired_line_shape mate st l2 Hm Hsafe Hl2 H2) as [c2 [Hc2 [Hd2 [Hne2 [R2 _]]]]].
    pose proof (locked_line_cell_bound l1 c1 Hl1 Hc1) as Hb1.
    pose proof (locked_line_cell_bound l2 c2 Hl2 Hc2) as Hb2.
    destruct (Hm c1 Hb1) as [_ Hinv1].
    assert (Hboth : In c1 l2 /\ In (mate c1) l2).
    { destruct (pair_region_cases mate c1 c2 Hm Hb1 Hb2 ltac:(congruence)) as [->| ->].
      - split; assumption.
      - rewrite Hinv1 in Hd2. split; assumption. }
    destruct Hboth as [Hc12 Hd12].
    destruct (list_eq_dec Nat.eq_dec l1 l2) as [Heq|Hneq]; [exact Heq|exfalso].
    destruct (ForallOrdPairs_In lines_meet_once l1 l2 Hl1 Hl2) as [Heq|[H|H]];
      [contradiction| |].
    + exact (H c1 (mate c1) (not_eq_sym Hne1) Hc1 Hd1 Hc12 Hd12).
    + exact (H c1 (mate c1) (not_eq_sym Hne1) Hc12 Hd12 Hc1 Hd1).
Qed.

(** Corollary: the existing pairing impossibility, re-derived through the
    regional density bound. *)
Corollary no_pairing_leaf_at_empty_board mate :
  well_mated mate -> ~ pairing_safe mate initial_state.
Proof.
  intros Hm Hsafe.
  exact (empty_board_has_no_regional_certificate _ _
           (pairing_leaf_is_regional mate initial_state Hm Hsafe)).
Qed.
Print Assumptions empty_board_has_no_regional_certificate.
Print Assumptions regional_certificate_nonloss.
Print Assumptions checked_regional_leaf_policy.
Print Assumptions pairing_leaf_is_regional.
Print Assumptions no_pairing_leaf_at_empty_board.
