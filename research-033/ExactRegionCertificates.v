(** Exact-Region and Adaptive Gadget Certificates for 5x5x5 Qubic.
    Unifies:
    1) Per-region safe invariants (`phi < 32 /\ phi + gain < 32`), covering
       standard pairs, Erdős-Selfridge regions, and depth-0 K_4 Veblen gadgets;
    2) Bounded bottom-up adaptive gadget DAG witnesses (`K_{3,3}`, `S_10`,
       `3R+3C+2D`, `4R+4C`, `Slice-14`) verified via `vm_compute` on binary `N`
       bitmasks, transitioning cleanly into per-region safe leaves, with
       black-stone subset monotonicity (`mask_subb`).

    Depends strictly on the unchanged pinned `QubicTrusted.Rules` and `QubicAgent`. *)
From Stdlib Require Import List Arith Bool Lia Permutation NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import Geometry Minimax RulesFacts SafePairing.
Import ListNotations.

(** ** 1. General arithmetic, list, and bitmask helpers *)

Lemma sum_map_add {A} (f g : A -> nat) l :
  list_sum (map (fun x => f x + g x) l) = list_sum (map f l) + list_sum (map g l).
Proof. induction l; simpl; lia. Qed.

Lemma sum_map_le {A} (f g : A -> nat) l :
  (forall x, In x l -> f x <= g x) -> list_sum (map f l) <= list_sum (map g l).
Proof.
  induction l as [|a t IH]; simpl; intros H; [lia|].
  assert (Ha : f a <= g a) by (apply H; auto).
  assert (Ht : list_sum (map f t) <= list_sum (map g t)) by (apply IH; intros; apply H; auto).
  lia.
Qed.

Lemma sum_map_ext_in {A} (f g : A -> nat) l :
  (forall x, In x l -> f x = g x) -> list_sum (map f l) = list_sum (map g l).
Proof.
  induction l as [|a t IH]; simpl; intros H; [reflexivity|].
  rewrite H, IH; auto.
Qed.

Lemma sum_map_term {A} (f : A -> nat) l x :
  In x l -> f x <= list_sum (map f l).
Proof.
  induction l as [|a t IH]; simpl; intros H; [contradiction|].
  destruct H as [->|Hx]; [lia|pose proof (IH Hx); lia].
Qed.

Lemma sum_map_const {A} (f : A -> nat) k l :
  (forall x, In x l -> f x = k) -> list_sum (map f l) = length l * k.
Proof.
  induction l as [|a t IH]; simpl; intros H; [lia|].
  rewrite H, IH by auto. lia.
Qed.

Lemma length_filter_le {A} (p : A -> bool) l : length (filter p l) <= length l.
Proof. induction l as [|a t IH]; simpl; [|destruct (p a); simpl]; lia. Qed.

Lemma sum_inj_le {A B} (h : A -> B) (f1 : A -> nat) (f2 : B -> nat) xs ys :
  (forall x1 x2, In x1 xs -> In x2 xs -> h x1 = h x2 -> x1 = x2) ->
  (forall x, In x xs -> In (h x) ys) ->
  (forall x, In x xs -> f1 x <= f2 (h x)) ->
  NoDup xs -> NoDup ys ->
  list_sum (map f1 xs) <= list_sum (map f2 ys).
Proof.
  revert ys. induction xs as [|a t IH]; intros ys Hinj Hin Hle Hndx Hndy; simpl; [lia|].
  inversion Hndx as [|? ? Hna Hndt]; subst.
  assert (Ha_in : In (h a) ys) by (apply Hin; left; reflexivity).
  destruct (in_split _ _ Ha_in) as [y1 [y2 Hy]].
  assert (Hnd12 : NoDup (y1 ++ y2)).
  { rewrite Hy in Hndy. exact (NoDup_remove_1 _ _ _ Hndy). }
  assert (Hsum_ys : list_sum (map f2 ys) = f2 (h a) + list_sum (map f2 (y1 ++ y2))).
  { rewrite Hy, !map_app, !list_sum_app. simpl. lia. }
  assert (Hrec : list_sum (map f1 t) <= list_sum (map f2 (y1 ++ y2))).
  { apply IH; try assumption.
    - intros x1 x2 H1 H2. apply Hinj; right; assumption.
    - intros x Hx. assert (Hx_in : In (h x) ys) by (apply Hin; right; assumption).
      rewrite Hy in Hx_in. destruct (in_app_or _ _ _ Hx_in) as [H|H]; [apply in_or_app; left; exact H|].
      destruct H as [Heq|H]; [|apply in_or_app; right; exact H].
      exfalso. apply Hna. rewrite <- (Hinj x a); [exact Hx|right; exact Hx|left; reflexivity|exact (eq_sym Heq)].
    - intros x Hx. apply Hle; right; exact Hx. }
  pose proof (Hle a (or_introl eq_refl)). lia.
Qed.

Lemma list_sum_map_nth_seq {A} (f : A -> nat) (l : list A) (d : A) :
  list_sum (map f l) = list_sum (map (fun k => f (nth k l d)) (seq 0 (length l))).
Proof.
  cut (forall off, list_sum (map f l) =
                   list_sum (map (fun k => f (nth (k - off) l d)) (seq off (length l)))).
  { intros H. specialize (H 0). simpl in H. rewrite H. apply sum_map_ext_in.
    intros k _. rewrite Nat.sub_0_r. reflexivity. }
  induction l as [|x xs IH]; intros off; simpl; [reflexivity|].
  rewrite Nat.sub_diag. f_equal. rewrite (IH (S off)). apply sum_map_ext_in.
  intros k Hk. apply in_seq in Hk.
  replace (k - off) with (S (k - S off)) by lia. reflexivity.
Qed.

Definition mem (c : cell) (xs : list cell) : bool := existsb (Nat.eqb c) xs.

Lemma mem_spec c xs : mem c xs = true <-> In c xs.
Proof. apply member_spec. Qed.

Fixpoint nodupb {A} (eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: t => negb (existsb (eqb x) t) && nodupb eqb t
  end.

Lemma nodupb_sound {A} (eqb : A -> A -> bool)
    (Heqb : forall x y, eqb x y = true <-> x = y) l :
  nodupb eqb l = true -> NoDup l.
Proof.
  induction l as [|x t IH]; simpl; intros H; [constructor|].
  apply andb_true_iff in H as [Hx Ht]. constructor; [|auto].
  apply negb_true_iff in Hx. intros Hin.
  assert (Hex : existsb (eqb x) t = true).
  { apply existsb_exists. exists x. split; [exact Hin|apply Heqb; reflexivity]. }
  congruence.
Qed.

Lemma nat_nodupb_sound l : nodupb Nat.eqb l = true -> NoDup l.
Proof. apply nodupb_sound. intros x y. apply Nat.eqb_eq. Qed.

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
  | _, _ => false
  end.

Lemma list_eqb_sound {A} (eqb : A -> A -> bool)
    (Heqb : forall x y, eqb x y = true <-> x = y) l1 l2 :
  list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  revert l2. induction l1 as [|x xs IH]; intros [|y ys]; simpl;
    try (split; [discriminate|intros H; discriminate]).
  - split; reflexivity.
  - rewrite andb_true_iff, Heqb, IH. split.
    + intros [-> ->]. reflexivity.
    + intros H. inversion H. auto.
Qed.

Definition list_nat_eqb := list_eqb Nat.eqb.

Lemma list_nat_eqb_eq l1 l2 : list_nat_eqb l1 l2 = true <-> l1 = l2.
Proof. apply list_eqb_sound. intros x y. apply Nat.eqb_eq. Qed.

Lemma all_lines_checks :
  forallb (nodupb Nat.eqb) all_lines = true /\
  forallb (fun l => length l =? 5) all_lines = true /\
  nodupb list_nat_eqb all_lines = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma line_nodup l : In l all_lines -> NoDup l.
Proof.
  intros Hl. destruct all_lines_checks as [H _].
  apply forallb_forall with (x := l) in H; [apply nat_nodupb_sound, H|exact Hl].
Qed.

Lemma line_length l : In l all_lines -> length l = 5.
Proof.
  intros Hl. destruct all_lines_checks as [_ [H _]].
  apply forallb_forall with (x := l) in H; [apply Nat.eqb_eq, H|exact Hl].
Qed.

Lemma all_lines_nodup : NoDup all_lines.
Proof.
  destruct all_lines_checks as [_ [_ H]].
  apply (nodupb_sound list_nat_eqb list_nat_eqb_eq), H.
Qed.

Lemma all_cells_spec z : In z all_cells <-> z < 125.
Proof. unfold all_cells. rewrite in_seq. lia. Qed.

Lemma NoDup_filter_eq_length {A} (p : A -> bool) l1 l2 :
  NoDup l1 -> NoDup l2 -> (forall c, In c l1 <-> In c l2) ->
  length (filter p l1) = length (filter p l2).
Proof.
  intros H1 H2 Heq. apply Nat.le_antisymm; apply NoDup_incl_length; try apply NoDup_filter; auto.
  - intros x Hx. apply filter_In in Hx as [Hx1 Hpx]. apply filter_In. split; [apply Heq, Hx1|exact Hpx].
  - intros x Hx. apply filter_In in Hx as [Hx2 Hpx]. apply filter_In. split; [apply Heq, Hx2|exact Hpx].
Qed.

Lemma NoDup_eq_length {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall c, In c l1 <-> In c l2) ->
  length l1 = length l2.
Proof.
  intros H1 H2 Heq. apply Nat.le_antisymm; apply NoDup_incl_length; auto.
  - intros x Hx. apply Heq, Hx.
  - intros x Hx. apply Heq, Hx.
Qed.

(** ** 2. Per-region Erdős–Selfridge invariant (`phi < 32 /\ phi + gain < 32`) *)

Definition add_white (st : GameState) (x : cell) : GameState :=
  make_state (x :: white_stones st) (black_stones st) (x :: history st).

Definition add_black (st : GameState) (y : cell) : GameState :=
  make_state (white_stones st) (y :: black_stones st) (y :: history st).

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

Lemma effective_legal st y : is_legal_move st y = true -> effective_move st y = y.
Proof. intros H. unfold effective_move. rewrite H. reflexivity. Qed.

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

Lemma best_none_nil f (l : list cell) : best f l = None -> l = [].
Proof.
  destruct l as [|c t]; [reflexivity|]. simpl.
  destruct (best f t); [destruct (f c <? f c0); discriminate|discriminate].
Qed.

Section PerRegion.

Variable reg : cell -> nat.
Variable asg : list cell -> nat.

Definition frag (l : list cell) : list cell := filter (fun c => reg c =? asg l) l.

Definition wcount (st : GameState) (l : list cell) : nat :=
  length (filter (fun c => mem c (white_stones st)) (frag l)).

Definition blocked (st : GameState) (l : list cell) : bool :=
  existsb (fun c => mem c (black_stones st)) l.

Definition weight (st : GameState) (l : list cell) : nat :=
  if blocked st l then 0 else 2 ^ (5 - length (frag l) + wcount st l).

Definition phi (st : GameState) (r : nat) : nat :=
  list_sum (map (fun l => if asg l =? r then weight st l else 0) all_lines).

Definition gain (st : GameState) (x : cell) : nat :=
  list_sum (map (fun l => if mem x (frag l) then weight st l else 0) all_lines).

Definition region_safe (st : GameState) (r : nat) : Prop :=
  phi st r < 32 /\
  forall c, c < 125 -> occupied st c = false -> reg c = r -> phi st r + gain st c < 32.

Lemma frag_reg l c : In c (frag l) -> reg c = asg l.
Proof. unfold frag. intros H. apply filter_In in H as [_ H]. apply Nat.eqb_eq, H. Qed.

Lemma frag_sub l c : In c (frag l) -> In c l.
Proof. unfold frag. intros H. apply filter_In in H as [H _]. exact H. Qed.

Lemma frag_nodup l : In l all_lines -> NoDup (frag l).
Proof. intros Hl. apply NoDup_filter, line_nodup, Hl. Qed.

Lemma frag_length l : In l all_lines -> length (frag l) <= 5.
Proof. intros Hl. rewrite <- (line_length l Hl). apply length_filter_le. Qed.

Lemma wcount_le_frag st l : wcount st l <= length (frag l).
Proof. apply length_filter_le. Qed.

Lemma below_32_line_no_white_win st l :
  valid_state st -> In l all_lines -> phi st (asg l) < 32 ->
  has_line (white_stones st) l = false.
Proof.
  intros Hvalid Hl Hphi. destruct (has_line (white_stones st) l) eqn:Hwin; [|reflexivity].
  exfalso.
  assert (Hall : forall c, In c l -> In c (white_stones st)).
  { intros c Hc. unfold has_line in Hwin.
    apply forallb_forall with (x := c) in Hwin; [apply mem_spec, Hwin|exact Hc]. }
  assert (Hw : weight st l = 32).
  { unfold weight, blocked, wcount.
    replace (existsb (fun c => mem c (black_stones st)) l) with false.
    - replace (filter (fun c => mem c (white_stones st)) (frag l)) with (frag l).
      + pose proof (frag_length l Hl). rewrite Nat.sub_add by exact H. reflexivity.
      + symmetry. apply forallb_filter_id. apply forallb_forall.
        intros c Hc. apply mem_spec, Hall, frag_sub, Hc.
    - symmetry. apply not_true_iff_false. intros Hb.
      apply existsb_exists in Hb as [c [Hc Hcb]]. apply mem_spec in Hcb.
      exact (valid_colors_disjoint st c Hvalid (Hall c Hc) Hcb). }
  pose proof (sum_map_term (fun g => if asg g =? asg l then weight st g else 0) all_lines l Hl) as Ht.
  cbn beta in Ht. rewrite Nat.eqb_refl, Hw in Ht. unfold phi in Hphi. lia.
Qed.

Lemma mem_cons c x W : mem c (x :: W) = (c =? x) || mem c W.
Proof. unfold mem. simpl. rewrite Nat.eqb_sym. reflexivity. Qed.

Lemma count_cons_member f x W :
  NoDup f -> ~ In x W ->
  length (filter (fun c => mem c (x :: W)) f) =
  (if mem x f then 1 else 0) + length (filter (fun c => mem c W) f).
Proof.
  induction 1 as [|a t Hna Ht IH]; [reflexivity|].
  intros HxW. cbn [filter].
  rewrite (mem_cons a x W), (mem_cons x a t), (Nat.eqb_sym a x).
  destruct (Nat.eqb_spec x a) as [->|Hxa].
  - rewrite !orb_true_l.
    assert (Hmat : mem a t = false)
      by (apply not_true_iff_false; intros H; apply Hna, mem_spec, H).
    destruct (mem a W) eqn:Ea; [exfalso; apply HxW; apply mem_spec, Ea|].
    cbv iota; cbn [length]. rewrite IH, Hmat by exact HxW. cbv iota. lia.
  - rewrite !orb_false_l.
    destruct (mem a W); cbv iota; cbn [length]; rewrite IH by exact HxW;
    destruct (mem x t); cbv iota; lia.
Qed.

Lemma weight_white st x l :
  ~ In x (white_stones st) -> In l all_lines ->
  weight (add_white st x) l = weight st l + if mem x (frag l) then weight st l else 0.
Proof.
  intros Hxw Hl. unfold weight, blocked, wcount. cbn [add_white white_stones black_stones].
  destruct (existsb (fun c => mem c (black_stones st)) l); [destruct (mem x (frag l)); lia|].
  rewrite count_cons_member by (try apply frag_nodup; assumption).
  destruct (mem x (frag l)) eqn:Hx.
  - pose proof (frag_length l Hl).
    assert (Hwc : length (filter (fun c => mem c (white_stones st)) (frag l)) <= length (frag l))
      by apply length_filter_le.
    replace (5 - length (frag l) + (1 + length (filter (fun c => mem c (white_stones st)) (frag l))))
      with (S (5 - length (frag l) + length (filter (fun c => mem c (white_stones st)) (frag l)))) by lia.
    simpl. lia.
  - rewrite Nat.add_0_l. lia.
Qed.

Lemma phi_white st x r :
  ~ In x (white_stones st) ->
  phi (add_white st x) r = phi st r + if reg x =? r then gain st x else 0.
Proof.
  intros Hxw. unfold phi, gain.
  transitivity (list_sum (map (fun l =>
    (if asg l =? r then weight st l else 0) +
    (if reg x =? r then if mem x (frag l) then weight st l else 0 else 0)) all_lines)).
  - apply sum_map_ext_in. intros l Hl. rewrite weight_white by assumption.
    destruct (asg l =? r) eqn:Er; destruct (mem x (frag l)) eqn:Hx; destruct (reg x =? r) eqn:Erx; try lia.
    + apply mem_spec, frag_reg in Hx. apply Nat.eqb_eq in Er. apply Nat.eqb_neq in Erx. congruence.
    + apply mem_spec, frag_reg in Hx. apply Nat.eqb_neq in Er. apply Nat.eqb_eq in Erx. congruence.
  - rewrite sum_map_add. destruct (reg x =? r); [reflexivity|].
    rewrite (sum_map_const (fun _ : list cell => 0) 0) by auto. lia.
Qed.

Lemma gain_white_other st x c :
  ~ In x (white_stones st) -> reg x <> reg c -> gain (add_white st x) c = gain st c.
Proof.
  intros Hxw Hne. unfold gain. apply sum_map_ext_in. intros l Hl.
  destruct (mem c (frag l)) eqn:Hc; [|reflexivity].
  rewrite weight_white by assumption.
  destruct (mem x (frag l)) eqn:Hx; [|lia].
  apply mem_spec, frag_reg in Hc. apply mem_spec, frag_reg in Hx. congruence.
Qed.

Lemma blocked_black_mono st y l :
  blocked st l = true -> blocked (add_black st y) l = true.
Proof.
  unfold blocked. cbn [add_black black_stones]. intros H.
  apply existsb_exists in H as [c [Hc Hmem]]. apply existsb_exists. exists c. split; [exact Hc|].
  rewrite mem_cons, Hmem, orb_true_r. reflexivity.
Qed.

Lemma weight_black_le st y l : weight (add_black st y) l <= weight st l.
Proof.
  unfold weight. destruct (blocked st l) eqn:Hb.
  - rewrite (blocked_black_mono st y l Hb). lia.
  - destruct (blocked (add_black st y) l); [lia|].
    unfold wcount. cbn [add_black white_stones]. lia.
Qed.

Lemma weight_black_zero st y l : In y (frag l) -> weight (add_black st y) l = 0.
Proof.
  intros Hy. unfold weight.
  replace (blocked (add_black st y) l) with true; [reflexivity|].
  symmetry. unfold blocked. apply existsb_exists. exists y.
  split; [exact (frag_sub l y Hy)|]. cbn [add_black black_stones].
  rewrite mem_cons, Nat.eqb_refl. reflexivity.
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

Lemma phi_black_gain st y :
  phi (add_black st y) (reg y) + gain st y <= phi st (reg y).
Proof.
  unfold phi, gain. rewrite <- sum_map_add. apply sum_map_le. intros l Hl.
  destruct (mem y (frag l)) eqn:Hy.
  - pose proof Hy as Hy'. apply mem_spec in Hy'. rewrite (frag_reg l y Hy'), Nat.eqb_refl.
    rewrite weight_black_zero by exact Hy'. lia.
  - destruct (asg l =? reg y); [pose proof (weight_black_le st y l); lia|lia].
Qed.

Definition candidates_in (cs : list cell) (st : GameState) (x : cell) : list cell :=
  filter (fun c => (reg c =? reg x) && negb (occupied st c)) cs.

Definition candidates (st : GameState) (x : cell) : list cell := candidates_in all_cells st x.

Lemma candidates_intro st x c :
  c < 125 -> occupied st c = false -> reg c = reg x -> In c (candidates st x).
Proof.
  intros Hc Hfree Hrc. unfold candidates, candidates_in. apply filter_In.
  split; [apply all_cells_spec, Hc|]. rewrite Hrc, Nat.eqb_refl, Hfree. reflexivity.
Qed.

Opaque all_cells.
Lemma candidates_elim st x y :
  In y (candidates st x) -> is_legal_move st y = true /\ reg y = reg x.
Proof.
  intros Hy. unfold candidates, candidates_in in Hy. apply filter_In in Hy as [Hy Hy'].
  apply andb_true_iff in Hy' as [Hry Hfy]. apply Nat.eqb_eq in Hry. split; [|exact Hry].
  unfold is_legal_move. apply andb_true_iff. split; [|exact Hfy].
  apply Nat.ltb_lt, all_cells_spec, Hy.
Qed.
Transparent all_cells.

Definition best_in_region (st : GameState) (x : cell) : cell :=
  match best (gain st) (candidates st x) with Some y => y | None => 0 end.

Lemma region_safe_other_preserved st request y r :
  valid_state st -> length (history st) < 125 -> region_safe st r ->
  reg (effective_move st request) <> r ->
  region_safe (move_state false (move_state true st request) y) r.
Proof.
  intros Hvalid Hlen [Hp Hg] Hne.
  pose proof (effective_move_is_legal st request Hvalid Hlen) as Hleg.
  destruct (legal_move_fresh st _ Hleg) as [_ [Hxw _]].
  set (x := effective_move st request).
  change (move_state true st request) with (add_white st x).
  set (y' := effective_move (add_white st x) y).
  change (move_state false (add_white st x) y) with (add_black (add_white st x) y').
  split.
  - pose proof (phi_black_le (add_white st x) y' r) as Hpb.
    rewrite phi_white in Hpb by exact Hxw.
    destruct (reg x =? r) eqn:E; [apply Nat.eqb_eq in E; exfalso; apply Hne; exact E|lia].
  - intros c Hc Hfree Hrc.
    destruct (occupied_add_black _ y' c Hfree) as [_ Hfree1].
    destruct (occupied_add_white st x c Hfree1) as [_ Hfree0].
    pose proof (phi_black_le (add_white st x) y' r) as Hpb.
    pose proof (gain_black_le (add_white st x) y' c) as Hgb.
    rewrite phi_white in Hpb by exact Hxw.
    destruct (reg x =? r) eqn:E; [apply Nat.eqb_eq in E; exfalso; apply Hne; exact E|].
    rewrite gain_white_other in Hgb by (try assumption; rewrite Hrc; exact Hne).
    specialize (Hg c Hc Hfree0 Hrc). lia.
Qed.

Lemma region_safe_black_any st y r :
  region_safe st r -> region_safe (add_black st y) r.
Proof.
  intros [Hp Hg]. split.
  - pose proof (phi_black_le st y r). lia.
  - intros c Hc Hfree Hrc.
    destruct (occupied_add_black st y c Hfree) as [_ Hfree0].
    pose proof (phi_black_le st y r).
    pose proof (gain_black_le st y c).
    specialize (Hg c Hc Hfree0 Hrc). lia.
Qed.

Lemma region_safe_reply_preserved st request :
  valid_state st -> length (history st) < 125 ->
  let x := effective_move st request in
  region_safe st (reg x) ->
  let st1 := move_state true st request in
  let y := best_in_region st1 x in
  region_safe (move_state false st1 y) (reg x) /\
  (forall c, In c (candidates st1 x) -> is_legal_move st1 y = true /\ reg y = reg x).
Proof.
  intros Hvalid Hlen x [Hp Hg] st1 y.
  pose proof (effective_move_is_legal st request Hvalid Hlen) as Hleg.
  destruct (legal_move_fresh st _ Hleg) as [Hxbound [Hxw _]].
  assert (Hxfree : occupied st x = false)
    by (unfold is_legal_move in Hleg; apply andb_true_iff in Hleg as [_ H]; apply negb_true_iff, H).
  assert (Hphi1 : phi st1 (reg x) < 32).
  { change st1 with (add_white st x). rewrite phi_white by exact Hxw.
    rewrite Nat.eqb_refl. apply Hg; [exact Hxbound|exact Hxfree|reflexivity]. }
  destruct (best (gain st1) (candidates st1 x)) as [y0|] eqn:Hb.
  - destruct (best_spec _ _ _ Hb) as [Hy0 Hmax].
    destruct (candidates_elim _ _ _ Hy0) as [Hlegy Hry].
    assert (Hy_eq : y = y0) by (unfold y, best_in_region; rewrite Hb; reflexivity).
    rewrite Hy_eq. split; [split|intros _ _; split; assumption].
    + change (move_state false st1 y0) with (add_black st1 (effective_move st1 y0)).
      rewrite (effective_legal _ _ Hlegy).
      pose proof (phi_black_le st1 y0 (reg x)). lia.
    + intros c Hc Hfree Hrc.
      change (move_state false st1 y0) with (add_black st1 (effective_move st1 y0)) in Hfree |- *.
      rewrite (effective_legal _ _ Hlegy) in Hfree |- *.
      destruct (occupied_add_black _ y0 c Hfree) as [_ Hfree1].
      pose proof (phi_black_gain st1 y0) as Hpg. rewrite Hry in Hpg.
      pose proof (gain_black_le st1 y0 c) as Hgb.
      assert (Hin : In c (candidates st1 x)) by (apply candidates_intro; assumption).
      assert (Hle : gain st1 c <= gain st1 y0) by (apply Hmax, Hin).
      lia.
  - apply best_none_nil in Hb.
    split; [split|].
    + change (move_state false st1 y) with (add_black st1 (effective_move st1 y)).
      pose proof (phi_black_le st1 (effective_move st1 y) (reg x)). lia.
    + intros c Hc Hfree Hrc.
      change (move_state false st1 y) with (add_black st1 (effective_move st1 y)) in Hfree |- *.
      destruct (occupied_add_black _ (effective_move st1 y) c Hfree) as [_ Hfree1].
      pose proof (candidates_intro st1 x c Hc Hfree1 Hrc) as Hin.
      rewrite Hb in Hin. contradiction.
    + intros c Hin. rewrite Hb in Hin. contradiction.
Qed.

Definition region_safeb (st : GameState) (r : nat) : bool :=
  (phi st r <? 32) &&
  forallb (fun c => if (reg c =? r) && negb (occupied st c)
                   then (phi st r + gain st c <? 32) else true) all_cells.

Lemma region_safeb_sound st r : region_safeb st r = true -> region_safe st r.
Proof.
  unfold region_safeb. rewrite andb_true_iff, Nat.ltb_lt, forallb_forall.
  intros [Hp Hg]. split; [exact Hp|].
  intros c Hc Hfree Hrc.
  assert (Hin : In c all_cells) by (apply all_cells_spec, Hc).
  specialize (Hg c Hin). rewrite Hrc, Nat.eqb_refl, Hfree in Hg.
  simpl in Hg. apply Nat.ltb_lt, Hg.
Qed.

Lemma region_safeb_complete st r : region_safe st r -> region_safeb st r = true.
Proof.
  intros [Hp Hg]. unfold region_safeb. rewrite andb_true_iff, Nat.ltb_lt, forallb_forall.
  split; [exact Hp|]. intros c Hc. apply all_cells_spec in Hc.
  destruct (reg c =? r) eqn:Er; destruct (occupied st c) eqn:Eo; simpl; try reflexivity.
  apply Nat.ltb_lt, Hg; [exact Hc|exact Eo|apply Nat.eqb_eq, Er].
Qed.

End PerRegion.

(** ** 3. Abstract N-bitmask subgame & bottom-up DAG verification *)

Definition mem_nat (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.

Lemma mem_nat_spec i l : mem_nat i l = true <-> In i l.
Proof. apply member_spec. Qed.

Definition frag_blocked (b_bb : N) (f : list nat) : bool :=
  existsb (fun i => N.testbit b_bb (N.of_nat i)) f.

Definition frag_won (m_bb : N) (f : list nat) : bool :=
  forallb (fun i => N.testbit m_bb (N.of_nat i)) f.

Definition no_frag_win (frags : list (list nat)) (m_bb : N) : bool :=
  negb (existsb (frag_won m_bb) frags).

Definition frag_rem_count (m_bb b_bb : N) (f : list nat) : nat :=
  length (filter (fun i => negb (N.testbit m_bb (N.of_nat i) || N.testbit b_bb (N.of_nat i))) f).

Definition sub_weight (m_bb b_bb : N) (f : list nat) : nat :=
  if frag_blocked b_bb f then 0 else 2 ^ (5 - frag_rem_count m_bb b_bb f).

Definition sub_phi (frags : list (list nat)) (m_bb b_bb : N) : nat :=
  list_sum (map (sub_weight m_bb b_bb) frags).

Definition sub_gain (frags : list (list nat)) (m_bb b_bb : N) (i : nat) : nat :=
  list_sum (map (fun f => if mem_nat i f then sub_weight m_bb b_bb f else 0) frags).

Definition sub_safeb (n : nat) (frags : list (list nat)) (m_bb b_bb : N) : bool :=
  (sub_phi frags m_bb b_bb <? 32) &&
  forallb (fun i => if negb (N.testbit m_bb (N.of_nat i) || N.testbit b_bb (N.of_nat i))
                   then (sub_phi frags m_bb b_bb + sub_gain frags m_bb b_bb i <? 32)
                   else true) (seq 0 n).

Record GadgetSpec := mk_gadget_spec {
  gs_n : nat;
  gs_frags : list (list nat);
  gs_nodes : list (N * N);
  gs_replies : list (N * N * nat)
}.

Definition mask_subb (sub sup : N) : bool := N.eqb (N.land sub sup) sub.

Lemma mask_subb_iff sub sup :
  mask_subb sub sup = true <-> (forall k, N.testbit sub k = true -> N.testbit sup k = true).
Proof.
  unfold mask_subb. rewrite N.eqb_eq, <- N.bits_inj_iff.
  split; intros H k.
  - intros Hk. specialize (H k). rewrite N.land_spec, Hk in H. destruct (N.testbit sup k); [reflexivity|discriminate].
  - rewrite N.land_spec. destruct (N.testbit sub k) eqn:Es; [rewrite (H k Es); reflexivity|reflexivity].
Qed.

Lemma mask_subb_refl m : mask_subb m m = true.
Proof. apply mask_subb_iff. auto. Qed.

Lemma mask_subb_trans a b c :
  mask_subb a b = true -> mask_subb b c = true -> mask_subb a c = true.
Proof.
  rewrite !mask_subb_iff. intros H1 H2 k Hk. apply H2, H1, Hk.
Qed.

Lemma mask_subb_setbit_both a b k :
  mask_subb a b = true -> mask_subb (N.setbit a k) (N.setbit b k) = true.
Proof.
  rewrite !mask_subb_iff. intros H j Hj.
  rewrite N.setbit_iff in Hj. apply N.setbit_iff. destruct Hj as [<-|Hj]; [left; reflexivity|right; apply H, Hj].
Qed.

Lemma mask_subb_setbit_left a b k :
  mask_subb a b = true -> N.testbit b k = true -> mask_subb (N.setbit a k) b = true.
Proof.
  rewrite !mask_subb_iff. intros H Hb j Hj.
  rewrite N.setbit_iff in Hj. destruct Hj as [<-|Hj]; [exact Hb|apply H, Hj].
Qed.

Lemma mask_subb_0 sup : mask_subb 0%N sup = true.
Proof. apply mask_subb_iff. intros k Hk. rewrite N.bits_0 in Hk. discriminate. Qed.

Definition assoc_reply (replies : list (N * N * nat)) (m b : N) : option nat :=
  match find (fun e => N.eqb (fst (fst e)) m && N.eqb (snd (fst e)) b) replies with
  | Some (_, v) => Some v
  | None => None
  end.

Definition find_shadow_reply (replies : list (N * N * nat)) (m b_real : N) : option (N * nat) :=
  match find (fun e => N.eqb (fst (fst e)) m && mask_subb (snd (fst e)) b_real) replies with
  | Some ((_, be), v) => Some (be, v)
  | None => None
  end.

Definition has_pair (m b : N) (xs : list (N * N)) : bool :=
  existsb (fun p => N.eqb (fst p) m && N.eqb (snd p) b) xs.

Fixpoint check_nodes_bu (n : nat) (frags : list (list nat)) (replies : list (N * N * nat))
    (verified : list (N * N)) (nodes : list (N * N)) : bool :=
  match nodes with
  | [] => true
  | (m, b) :: rest =>
      let ok_node :=
        no_frag_win frags m &&
        forallb (fun u =>
          if N.testbit m (N.of_nat u) || N.testbit b (N.of_nat u) then true
          else
            let m' := N.setbit m (N.of_nat u) in
            no_frag_win frags m' &&
            match assoc_reply replies m' b with
            | None => false
            | Some v =>
                (v <? n) && negb (v =? u) &&
                negb (N.testbit m (N.of_nat v) || N.testbit b (N.of_nat v)) &&
                let b' := N.setbit b (N.of_nat v) in
                sub_safeb n frags m' b' || has_pair m' b' verified
            end) (seq 0 n) in
      ok_node && check_nodes_bu n frags replies ((m, b) :: verified) rest
  end.

Definition check_replies_closed (n : nat) (frags : list (list nat))
    (nodes : list (N * N)) (replies : list (N * N * nat)) : bool :=
  forallb (fun '((m', b), v) =>
    no_frag_win frags m' &&
    (v <? n) &&
    negb (N.testbit m' (N.of_nat v) || N.testbit b (N.of_nat v)) &&
    let b' := N.setbit b (N.of_nat v) in
    sub_safeb n frags m' b' || has_pair m' b' nodes) replies.

Definition verify_gadgetb (gs : GadgetSpec) : bool :=
  forallb (fun f => nodupb Nat.eqb f && forallb (fun i => i <? gs_n gs) f) (gs_frags gs) &&
  check_nodes_bu (gs_n gs) (gs_frags gs) (gs_replies gs) [] (gs_nodes gs) &&
  check_replies_closed (gs_n gs) (gs_frags gs) (gs_nodes gs) (gs_replies gs) &&
  (sub_safeb (gs_n gs) (gs_frags gs) 0%N 0%N || has_pair 0%N 0%N (gs_nodes gs)).

Inductive sub_safe (frags : list (list nat)) (n : nat) (replies : list (N * N * nat)) : N -> N -> Prop :=
| sub_safe_base : forall m b,
    sub_safeb n frags m b = true -> sub_safe frags n replies m b
| sub_safe_step : forall m b,
    no_frag_win frags m = true ->
    (forall u, u < n -> N.testbit m (N.of_nat u) = false -> N.testbit b (N.of_nat u) = false ->
      let m' := N.setbit m (N.of_nat u) in
      no_frag_win frags m' = true /\
      exists v, assoc_reply replies m' b = Some v /\
                v < n /\ v <> u /\ N.testbit m (N.of_nat v) = false /\ N.testbit b (N.of_nat v) = false /\
                sub_safe frags n replies m' (N.setbit b (N.of_nat v))) ->
    sub_safe frags n replies m b.

Lemma has_pair_spec m b xs : has_pair m b xs = true <-> In (m, b) xs.
Proof.
  unfold has_pair. rewrite existsb_exists. split.
  - intros [[m0 b0] [Hin H]]. apply andb_true_iff in H as [H1 H2].
    cbn [fst snd] in H1, H2. apply N.eqb_eq in H1. apply N.eqb_eq in H2. subst. exact Hin.
  - intros Hin. exists (m, b). split; [exact Hin|].
    cbn [fst snd]. rewrite !N.eqb_refl. reflexivity.
Qed.

Lemma check_nodes_bu_sound n frags replies verified nodes :
  check_nodes_bu n frags replies verified nodes = true ->
  (forall m b, In (m, b) verified -> sub_safe frags n replies m b) ->
  (forall m b, In (m, b) nodes -> sub_safe frags n replies m b).
Proof.
  revert verified. induction nodes as [|[m0 b0] rest IH]; intros verified Hchk Hver m b Hin.
  - contradiction.
  - cbn [check_nodes_bu] in Hchk. apply andb_true_iff in Hchk as [Hnode Hrest].
    apply andb_true_iff in Hnode as [Hnw Hforall].
    assert (Hcur : sub_safe frags n replies m0 b0).
    { apply sub_safe_step; [exact Hnw|].
      intros u Hu Hmu Hbu. rewrite forallb_forall in Hforall.
      assert (Huin : In u (seq 0 n)) by (apply in_seq; lia).
      specialize (Hforall u Huin).
      rewrite Hmu, Hbu in Hforall. simpl in Hforall.
      apply andb_true_iff in Hforall as [Hnw' Hm].
      split; [exact Hnw'|].
      destruct (assoc_reply replies (N.setbit m0 (N.of_nat u)) b0) as [v|] eqn:Ha; [|discriminate].
      exists v.
      apply andb_true_iff in Hm as [Hm Hsafe].
      apply andb_true_iff in Hm as [Hm Hfreev].
      apply andb_true_iff in Hm as [Hvn Hvu].
      apply Nat.ltb_lt in Hvn. apply negb_true_iff, Nat.eqb_neq in Hvu.
      apply negb_true_iff, orb_false_iff in Hfreev as [Hmv Hbv].
      repeat split; try assumption.
      apply orb_true_iff in Hsafe as [Hs|Hp].
      - apply sub_safe_base, Hs.
      - apply has_pair_spec in Hp. apply Hver, Hp. }
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst. exact Hcur.
    + apply (IH ((m0, b0) :: verified) Hrest); [|exact Hin].
      intros m1 b1 [Heq1|Hin1]; [inversion Heq1; subst; exact Hcur|apply Hver, Hin1].
Qed.

Lemma verify_gadgetb_sound gs :
  verify_gadgetb gs = true ->
  sub_safe (gs_frags gs) (gs_n gs) (gs_replies gs) 0%N 0%N.
Proof.
  unfold verify_gadgetb.
  intros H.
  apply andb_true_iff in H as [H H0].
  apply andb_true_iff in H as [H Hclosed].
  apply andb_true_iff in H as [Hfr Hnodes].
  apply orb_true_iff in H0 as [Hs|Hp].
  - apply sub_safe_base, Hs.
  - apply has_pair_spec in Hp.
    eapply check_nodes_bu_sound; [exact Hnodes|intros; contradiction|exact Hp].
Qed.

Lemma verify_gadgetb_replies gs m' be v :
  verify_gadgetb gs = true ->
  In ((m', be), v) (gs_replies gs) ->
  no_frag_win (gs_frags gs) m' = true /\
  v < gs_n gs /\
  N.testbit m' (N.of_nat v) = false /\
  N.testbit be (N.of_nat v) = false /\
  sub_safe (gs_frags gs) (gs_n gs) (gs_replies gs) m' (N.setbit be (N.of_nat v)).
Proof.
  unfold verify_gadgetb. intros H Hin.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hclosed].
  apply andb_true_iff in H as [_ Hnodes].
  unfold check_replies_closed in Hclosed. rewrite forallb_forall in Hclosed.
  specialize (Hclosed _ Hin).
  apply andb_true_iff in Hclosed as [Hm Hsafe].
  apply andb_true_iff in Hm as [Hm Hfreev].
  apply andb_true_iff in Hm as [Hnw Hvn].
  apply Nat.ltb_lt in Hvn. apply negb_true_iff, orb_false_iff in Hfreev as [Hmv Hbv].
  repeat split; try assumption.
  apply orb_true_iff in Hsafe as [Hs|Hp].
  - apply sub_safe_base, Hs.
  - apply has_pair_spec in Hp.
    eapply check_nodes_bu_sound; [exact Hnodes|intros; contradiction|exact Hp].
Qed.

Lemma find_shadow_reply_some replies m' b0 v0 b_real :
  assoc_reply replies m' b0 = Some v0 ->
  mask_subb b0 b_real = true ->
  exists be v,
    find_shadow_reply replies m' b_real = Some (be, v) /\
    In ((m', be), v) replies /\
    mask_subb be b_real = true.
Proof.
  unfold assoc_reply, find_shadow_reply. intros Ha Hsub.
  destruct (find (fun e => N.eqb (fst (fst e)) m' && N.eqb (snd (fst e)) b0) replies)
    as [[[m0 b0'] v0']|] eqn:Ef; [|discriminate].
  apply find_some in Ef as [Hin0 Hp0]. cbn [fst snd] in Hp0.
  apply andb_true_iff in Hp0 as [Hm0 Hb0]. apply N.eqb_eq in Hm0. apply N.eqb_eq in Hb0. subst.
  destruct (find (fun e => N.eqb (fst (fst e)) m' && mask_subb (snd (fst e)) b_real) replies)
    as [[[me be] ve]|] eqn:Ef2.
  - apply find_some in Ef2 as [Hin2 Hp2]. cbn [fst snd] in Hp2.
    apply andb_true_iff in Hp2 as [Hme Hbe]. apply N.eqb_eq in Hme. subst.
    exists be, ve. repeat split; assumption.
  - exfalso. pose proof (find_none _ _ Ef2 _ Hin0) as Hnone.
    cbn [fst snd] in Hnone. rewrite N.eqb_refl, Hsub in Hnone. discriminate.
Qed.

(** ** 4. Embedding subgames into `GameState` and global `HybridCert` theorem *)

Fixpoint local_mask_aux (k : nat) (stones : list cell) (embed : list cell) : N :=
  match embed with
  | [] => 0%N
  | c :: rest =>
      let tail := local_mask_aux (S k) stones rest in
      if mem c stones then N.setbit tail (N.of_nat k) else tail
  end.

Definition local_mask (stones : list cell) (embed : list cell) : N :=
  local_mask_aux 0 stones embed.

Lemma local_mask_aux_low k stones embed i :
  i < k -> N.testbit (local_mask_aux k stones embed) (N.of_nat i) = false.
Proof.
  revert k. induction embed as [|c rest IH]; intros k Hik; simpl.
  - exact (N.bits_0 (N.of_nat i)).
  - destruct (mem c stones).
    + rewrite N.setbit_neq; [apply IH; lia|].
      intros H. apply Nat2N.inj in H. lia.
    + apply IH; lia.
Qed.

Lemma local_mask_aux_bit k stones embed i :
  N.testbit (local_mask_aux k stones embed) (N.of_nat (k + i)) =
  if i <? length embed then mem (nth i embed 0) stones else false.
Proof.
  revert k i. induction embed as [|c rest IH]; intros k i; simpl.
  - destruct i; reflexivity.
  - destruct i as [|i'].
    + rewrite Nat.add_0_r. destruct (mem c stones) eqn:Em.
      * rewrite N.setbit_eq. reflexivity.
      * rewrite local_mask_aux_low by lia. reflexivity.
    + replace (k + S i') with (S k + i') by lia. destruct (mem c stones).
      * rewrite N.setbit_neq; [apply IH|intros H; apply Nat2N.inj in H; lia].
      * apply IH.
Qed.

Lemma local_mask_bit stones embed i :
  N.testbit (local_mask stones embed) (N.of_nat i) =
  if i <? length embed then mem (nth i embed 0) stones else false.
Proof. apply (local_mask_aux_bit 0 stones embed i). Qed.

Lemma NoDup_nth_inj {A} (l : list A) d i j :
  NoDup l -> i < length l -> j < length l -> nth i l d = nth j l d -> i = j.
Proof. intros Hnd. exact (proj1 (NoDup_nth l d) Hnd i j). Qed.

Lemma local_mask_add stones embed u x :
  NoDup embed -> u < length embed -> x = nth u embed 0 ->
  local_mask (x :: stones) embed = N.setbit (local_mask stones embed) (N.of_nat u).
Proof.
  intros Hnd Hu ->. change cell with nat in *. apply N.bits_inj. intros bn.
  rewrite <- (N2Nat.id bn). generalize (N.to_nat bn) as i. intros i.
  rewrite N.setbit_eqb, !local_mask_bit. change cell with nat in *.
  destruct (Nat.eqb_spec u i) as [<-|Hui].
  - rewrite N.eqb_refl.
    destruct (u <? length embed) eqn:Eu; [|apply Nat.ltb_ge in Eu; lia].
    rewrite mem_cons, Nat.eqb_refl. reflexivity.
  - assert (Hbn : (N.of_nat u =? N.of_nat i)%N = false).
    { apply N.eqb_neq. intros H. apply Nat2N.inj in H. congruence. }
    rewrite Hbn. destruct (i <? length embed) eqn:Hi; [|reflexivity].
    apply Nat.ltb_lt in Hi. rewrite mem_cons.
    assert (Hcell : (nth i embed 0 =? nth u embed 0) = false).
    { apply Nat.eqb_neq. intros H. apply Hui. eapply NoDup_nth_inj; eauto. }
    rewrite Hcell. reflexivity.
Qed.

Lemma local_mask_other stones embed x :
  ~ In x embed -> local_mask (x :: stones) embed = local_mask stones embed.
Proof.
  intros Hnotin. apply N.bits_inj. intros bn.
  rewrite <- (N2Nat.id bn). generalize (N.to_nat bn) as i. intros i.
  rewrite !local_mask_bit. destruct (i <? length embed) eqn:Hi; [|reflexivity].
  apply Nat.ltb_lt in Hi. rewrite mem_cons.
  assert (Hneq : (nth i embed 0 =? x) = false).
  { apply Nat.eqb_neq. intros <-. apply Hnotin, nth_In, Hi. }
  rewrite Hneq. reflexivity.
Qed.

Lemma local_mask_incl s1 s2 embed :
  incl s1 s2 -> mask_subb (local_mask s1 embed) (local_mask s2 embed) = true.
Proof.
  intros Hincl. apply mask_subb_iff. intros bn.
  rewrite <- (N2Nat.id bn). generalize (N.to_nat bn) as i. intros i.
  rewrite !local_mask_bit. destruct (i <? length embed); [|discriminate].
  rewrite !mem_spec. apply Hincl.
Qed.

Lemma local_mask_nil embed : local_mask [] embed = 0%N.
Proof.
  apply N.bits_inj. intros bn. rewrite <- (N2Nat.id bn).
  rewrite N.bits_0, local_mask_bit. destruct (N.to_nat bn <? length embed); reflexivity.
Qed.

Lemma local_mask_all_false stones embed :
  Forall (fun c => mem c stones = false) embed -> local_mask stones embed = 0%N.
Proof.
  intros Hall. apply N.bits_inj. intros bn. rewrite <- (N2Nat.id bn).
  rewrite N.bits_0, local_mask_bit. destruct (N.to_nat bn <? length embed) eqn:Hi; [|reflexivity].
  apply Nat.ltb_lt in Hi. rewrite Forall_forall in Hall. apply Hall, nth_In, Hi.
Qed.

Definition same_elemb (l1 l2 : list cell) : bool :=
  forallb (fun c => mem c l2) l1 && forallb (fun c => mem c l1) l2.

Lemma same_elemb_iff l1 l2 :
  same_elemb l1 l2 = true <-> (forall c, In c l1 <-> In c l2).
Proof.
  unfold same_elemb. rewrite andb_true_iff, !forallb_forall. split.
  - intros [H1 H2] c. split; intros Hc; apply mem_spec; [apply H1, Hc|apply H2, Hc].
  - intros Heq. split; intros c Hc; apply mem_spec, Heq, Hc.
Qed.

Record EmbeddedGadget := mk_emb_gadget {
  eg_reg_id : nat;
  eg_embed : list cell;
  eg_spec : GadgetSpec;
  eg_line_frags : list (list cell * nat)
}.

Definition gadget_compatb (reg : cell -> nat) (asg : list cell -> nat)
    (st0 : GameState) (g : EmbeddedGadget) : bool :=
  let r := eg_reg_id g in
  let embed := eg_embed g in
  let spec := eg_spec g in
  let ulines := filter (fun l => (asg l =? r) && negb (blocked st0 l)) all_lines in
  verify_gadgetb spec &&
  (length embed =? gs_n spec) &&
  nodupb Nat.eqb embed &&
  forallb (fun c => (c <? 125) && (reg c =? r) && negb (occupied st0 c)) embed &&
  forallb (fun c => if reg c =? r then mem c embed else true) all_cells &&
  forallb (fun f => nodupb Nat.eqb f && forallb (fun i => i <? gs_n spec) f) (gs_frags spec) &&
  list_eqb list_nat_eqb (map fst (eg_line_frags g)) ulines &&
  nodupb Nat.eqb (map snd (eg_line_frags g)) &&
  forallb (fun '(l, k) =>
    (k <? length (gs_frags spec)) &&
    same_elemb (frag reg asg l) (map (fun i => nth i embed 0) (nth k (gs_frags spec) [])))
    (eg_line_frags g).

Section HybridSoundness.

Variable reg : cell -> nat.
Variable asg : list cell -> nat.
Variable st0 : GameState.
Variable gs : list EmbeddedGadget.

Definition gadget_compat (g : EmbeddedGadget) : Prop :=
  gadget_compatb reg asg st0 g = true.

(* Cleanly split nested conjunctions in gadget_compatb *)
Lemma compat_elim g :
  gadget_compat g ->
  let r := eg_reg_id g in
  let embed := eg_embed g in
  let spec := eg_spec g in
  verify_gadgetb spec = true /\
  length embed = gs_n spec /\
  NoDup embed /\
  (forall c, In c embed -> c < 125 /\ reg c = r /\ occupied st0 c = false) /\
  (forall c, c < 125 -> reg c = r -> In c embed) /\
  (forall f, In f (gs_frags spec) -> NoDup f /\ forall i, In i f -> i < gs_n spec) /\
  map fst (eg_line_frags g) = filter (fun l => (asg l =? r) && negb (blocked st0 l)) all_lines /\
  NoDup (map snd (eg_line_frags g)) /\
  (forall l k, In (l, k) (eg_line_frags g) ->
    k < length (gs_frags spec) /\
    forall c, In c (frag reg asg l) <-> In c (map (fun i => nth i embed 0) (nth k (gs_frags spec) []))).
Proof.
  unfold gadget_compat, gadget_compatb. cbn zeta. intros H.
  apply andb_true_iff in H as [H H9].
  apply andb_true_iff in H as [H H8].
  apply andb_true_iff in H as [H H7].
  apply andb_true_iff in H as [H H6].
  apply andb_true_iff in H as [H H5].
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H2.
  apply nat_nodupb_sound in H3.
  apply (list_eqb_sound _ list_nat_eqb_eq) in H7.
  apply nat_nodupb_sound in H8.
  cbn zeta.
  split; [exact H1|].
  split; [exact H2|].
  split; [exact H3|].
  split; [intros c0 Hc; rewrite forallb_forall in H4; specialize (H4 c0 Hc);
          apply andb_true_iff in H4 as [H4 Hocc]; apply andb_true_iff in H4 as [Hc125 Hreg];
          apply Nat.ltb_lt in Hc125; apply Nat.eqb_eq in Hreg; apply negb_true_iff in Hocc; auto|].
  split; [intros c0 Hc Hrc; rewrite forallb_forall in H5; specialize (H5 c0 (proj2 (all_cells_spec c0) Hc));
          rewrite Hrc, Nat.eqb_refl in H5; apply mem_spec, H5|].
  split; [intros f Hf; rewrite forallb_forall in H6; specialize (H6 f Hf);
          apply andb_true_iff in H6 as [Hfnd Hfi]; rewrite forallb_forall in Hfi;
          split; [apply nat_nodupb_sound, Hfnd|intros i Hi; apply Nat.ltb_lt, Hfi, Hi]|].
  split; [exact H7|].
  split; [exact H8|].
  intros l k Hin. rewrite forallb_forall in H9. specialize (H9 (l, k) Hin).
  cbn iota in H9. apply andb_true_iff in H9 as [Hk Hsame].
  split; [apply Nat.ltb_lt, Hk|apply same_elemb_iff, Hsame].
Qed.

Lemma in_map_nth_embed f embed (k : nat) n :
  NoDup embed -> length embed = n -> NoDup f -> (forall i, In i f -> i < n) ->
  NoDup (map (fun i => nth i embed 0) f).
Proof.
  intros Hnd Hlen Hndf Hf. induction f as [|i ft IH]; simpl; [constructor|].
  inversion Hndf as [|? ? Hni Hndt]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as [j [Heq Hj]]. apply Hni.
    replace i with j; [exact Hj|].
    eapply NoDup_nth_inj; [exact Hnd|apply Hf; right; exact Hj|apply Hf; left; reflexivity|exact Heq].
  - apply IH; [exact Hndt|intros j Hj; apply Hf; right; exact Hj].
Qed.

Lemma map_nth_embed_in_iff embed i f n :
  NoDup embed -> length embed = n -> i < n -> (forall j, In j f -> j < n) ->
  In (nth i embed 0) (map (fun j => nth j embed 0) f) <-> In i f.
Proof.
  intros Hnd Hlen Hi Hf. split; intros H.
  - apply in_map_iff in H as [j [Heq Hj]].
    replace i with j; [exact Hj|]. eapply NoDup_nth_inj; [exact Hnd|rewrite Hlen; apply Hf, Hj|rewrite Hlen; exact Hi|exact Heq].
  - apply in_map_iff. exists i. auto.
Qed.

Lemma forallb_false_exists {A} (p : A -> bool) l :
  forallb p l = false -> exists x, In x l /\ p x = false.
Proof.
  induction l as [|x xs IH]; simpl; intros H; [discriminate|].
  apply andb_false_iff in H as [Hx|Hxs]; [exists x; auto|].
  destruct (IH Hxs) as [y [Hy1 Hy2]]. exists y. auto.
Qed.

Lemma gadget_no_white_win g st l :
  gadget_compat g ->
  valid_state st ->
  incl (black_stones st0) (black_stones st) ->
  In l all_lines ->
  asg l = eg_reg_id g ->
  no_frag_win (gs_frags (eg_spec g)) (local_mask (white_stones st) (eg_embed g)) = true ->
  has_line (white_stones st) l = false.
Proof.
  intros Hcomp Hvalid Hbincl Hl Hasg Hnw.
  destruct (has_line (white_stones st) l) eqn:Hw; [|reflexivity]. exfalso.
  assert (HallW : forall c, In c l -> In c (white_stones st)).
  { intros c Hc. unfold has_line in Hw. apply forallb_forall with (x := c) in Hw; [apply mem_spec, Hw|exact Hc]. }
  pose proof (compat_elim g Hcomp) as (_ & Hlen & Hnd & Hemb & _ & Hfr & Hmap & _ & Hlf).
  destruct (blocked st0 l) eqn:Hblk0.
  - unfold blocked in Hblk0. apply existsb_exists in Hblk0 as [c [Hcl Hcb]].
    apply mem_spec, Hbincl in Hcb. exact (valid_colors_disjoint st c Hvalid (HallW c Hcl) Hcb).
  - assert (Hin_ul : In l (filter (fun g0 => (asg g0 =? eg_reg_id g) && negb (blocked st0 g0)) all_lines)).
    { apply filter_In. split; [exact Hl|]. rewrite Hasg, Nat.eqb_refl, Hblk0. reflexivity. }
    rewrite <- Hmap in Hin_ul. apply in_map_iff in Hin_ul as [[l' k] [Heql Hpair]].
    cbn [fst] in Heql. subst l'.
    destruct (Hlf l k Hpair) as [Hk Hsame].
    set (f := nth k (gs_frags (eg_spec g)) []).
    assert (Hfin : In f (gs_frags (eg_spec g))) by (apply nth_In, Hk).
    assert (Hnot_won : frag_won (local_mask (white_stones st) (eg_embed g)) f = false).
    { unfold no_frag_win in Hnw. rewrite negb_true_iff in Hnw.
      destruct (frag_won (local_mask (white_stones st) (eg_embed g)) f) eqn:E; [|reflexivity].
      exfalso. assert (Hex : existsb (frag_won (local_mask (white_stones st) (eg_embed g))) (gs_frags (eg_spec g)) = true)
        by (apply existsb_exists; exists f; auto). congruence. }
    apply forallb_false_exists in Hnot_won as [i [Hi Hbit]].
    destruct (Hfr f Hfin) as [_ Hfi]. specialize (Hfi i Hi).
    rewrite <- Hlen in Hfi. rewrite local_mask_bit in Hbit.
    assert (Hilt : (i <? length (eg_embed g)) = true) by (apply Nat.ltb_lt, Hfi).
    rewrite Hilt in Hbit.
    set (c := nth i (eg_embed g) 0) in *.
    assert (Hc_frag : In c (frag reg asg l)).
    { apply Hsame, in_map_iff. exists i. auto. }
    assert (Hc_l : In c l) by (exact (frag_sub reg asg l c Hc_frag)).
    apply HallW, mem_spec in Hc_l. congruence.
Qed.

End HybridSoundness.

Lemma filter_map_ext {A B} (f : A -> B) (p1 : B -> bool) (p2 : A -> bool) l :
  (forall a, In a l -> p1 (f a) = p2 a) ->
  filter p1 (map f l) = map f (filter p2 l).
Proof.
  induction l as [|a t IH]; simpl; intros H; [reflexivity|].
  rewrite H by (left; reflexivity).
  destruct (p2 a); simpl; [f_equal|]; apply IH; intros; apply H; right; assumption.
Qed.

Section HybridSoundness2.

Variable reg : cell -> nat.
Variable asg : list cell -> nat.
Variable st0 : GameState.
Variable gs : list EmbeddedGadget.

Definition gadget_compat2 (g : EmbeddedGadget) : Prop :=
  gadget_compatb reg asg st0 g = true.

(* Re-open and finish cleanly *)
Lemma gadget_sub_safeb_to_region_safe g st b_virt :
  gadget_compatb reg asg st0 g = true ->
  valid_state st ->
  incl (black_stones st0) (black_stones st) ->
  mask_subb b_virt (local_mask (black_stones st) (eg_embed g)) = true ->
  sub_safeb (gs_n (eg_spec g)) (gs_frags (eg_spec g))
            (local_mask (white_stones st) (eg_embed g)) b_virt = true ->
  region_safe reg asg st (eg_reg_id g).
Proof.
  intros Hcomp Hvalid Hbincl Hsub Hsafe.
  pose proof (compat_elim reg asg st0 g Hcomp) as (_ & Hlen & Hnd & Hemb & Hallc & Hfr & Hmap & Hnd_k & Hlf).
  set (r := eg_reg_id g) in *.
  set (embed := eg_embed g) in *.
  set (frags := gs_frags (eg_spec g)) in *.
  set (m_bb := local_mask (white_stones st) embed) in *.
  set (n := gs_n (eg_spec g)) in *.
  assert (Hline_le : forall l k, In l all_lines -> In (l, k) (eg_line_frags g) ->
            weight reg asg st l <= sub_weight m_bb b_virt (nth k frags [])).
  { intros l k Hl Hpair. destruct (Hlf l k Hpair) as [Hk Hsame].
    set (f := nth k frags []).
    assert (Hfin : In f frags) by (apply nth_In, Hk).
    destruct (Hfr f Hfin) as [Hndf Hfi].
    unfold weight, sub_weight. destruct (blocked st l) eqn:Hbl; [lia|].
    destruct (frag_blocked b_virt f) eqn:Hfb.
    - exfalso. unfold frag_blocked in Hfb. apply existsb_exists in Hfb as [i [Hi Hbit]].
      rewrite mask_subb_iff in Hsub. specialize (Hsub _ Hbit).
      rewrite local_mask_bit in Hsub.
      assert (Hil : (i <? length embed) = true) by (apply Nat.ltb_lt; rewrite Hlen; apply Hfi, Hi).
      rewrite Hil in Hsub.
      assert (Hc_l : In (nth i embed 0) l) by (apply (frag_sub reg asg l), Hsame, in_map_iff; exists i; auto).
      unfold blocked in Hbl.
      assert (Hex : existsb (fun c => mem c (black_stones st)) l = true)
        by (apply existsb_exists; exists (nth i embed 0); auto). congruence.
    - assert (Hfree_len : length (frag reg asg l) - wcount reg asg st l =
                          length (filter (fun c => negb (mem c (white_stones st))) (frag reg asg l))).
      { unfold wcount.
        assert (Hpart : forall p (xs : list cell), length (filter p xs) + length (filter (fun x => negb (p x)) xs) = length xs).
        { induction xs; simpl; [lia|destruct (p a); simpl; lia]. }
        specialize (Hpart (fun c => mem c (white_stones st)) (frag reg asg l)). lia. }
      assert (Hle5 : length (frag reg asg l) <= 5) by (apply frag_length; exact Hl).
      assert (Hwc : wcount reg asg st l <= length (frag reg asg l)) by (apply wcount_le_frag).
      replace (5 - length (frag reg asg l) + wcount reg asg st l)
        with (5 - (length (frag reg asg l) - wcount reg asg st l)) by lia.
      rewrite Hfree_len.
      rewrite (@NoDup_filter_eq_length cell (fun c => negb (mem c (white_stones st)))
                 (frag reg asg l) (map (fun i => nth i embed 0) f));
        [|apply frag_nodup, Hl|apply (in_map_nth_embed f embed k n Hnd Hlen Hndf Hfi)|exact Hsame].
      unfold frag_rem_count.
      rewrite (filter_map_ext (fun i => nth i embed 0)
                 (fun c => negb (mem c (white_stones st)))
                 (fun i => negb (N.testbit m_bb (N.of_nat i) || N.testbit b_virt (N.of_nat i)))).
      + rewrite length_map. lia.
      + intros i Hi. unfold m_bb. rewrite local_mask_bit.
        assert (Hil : (i <? length embed) = true) by (apply Nat.ltb_lt; rewrite Hlen; apply Hfi, Hi).
        rewrite Hil. destruct (N.testbit b_virt (N.of_nat i)) eqn:Eb.
        * exfalso. unfold frag_blocked in Hfb.
          assert (Hex : existsb (fun j => N.testbit b_virt (N.of_nat j)) f = true)
            by (apply existsb_exists; exists i; auto). congruence.
        * rewrite orb_false_r. reflexivity. }

  (* Now deduce phi st r <= sub_phi frags m_bb b_virt and gain st c <= sub_gain frags m_bb b_virt i *)
  assert (Hphi_le : phi reg asg st r <= sub_phi frags m_bb b_virt).
  { unfold phi, sub_phi.
    set (ulines := filter (fun l => (asg l =? r) && negb (blocked st0 l)) all_lines).
    transitivity (list_sum (map (weight reg asg st) ulines)).
    - unfold ulines. clear -Hbincl. generalize all_lines as ls. induction ls as [|l ls IH]; simpl; [lia|].
      destruct (asg l =? r); destruct (blocked st0 l) eqn:Hb0; simpl; try lia.
      assert (Hw0 : weight reg asg st l = 0).
      { unfold weight. replace (blocked st l) with true; [reflexivity|].
        symmetry. unfold blocked in *. apply existsb_exists in Hb0 as [c [Hc Hcb]].
        apply existsb_exists. exists c. split; [exact Hc|apply mem_spec, Hbincl, mem_spec, Hcb]. }
      rewrite Hw0. lia.
    - unfold ulines. rewrite <- Hmap, (list_sum_map_nth_seq (sub_weight m_bb b_virt) frags []).
      rewrite map_map.
      (* Apply sum_inj_le from (eg_line_frags g) via snd into (seq 0 (length frags)) *)
      assert (Hnd_pairs : NoDup (eg_line_frags g)).
      { eapply NoDup_map_inv. exact Hnd_k. }
      eapply (sum_inj_le snd (fun p => weight reg asg st (fst p))
                            (fun k => sub_weight m_bb b_virt (nth k frags []))).
      + intros [l1 k1] [l2 k2] H1 H2 Heq. cbn [snd] in Heq. subst k2.
        (* k1 = k2 in map snd (eg_line_frags g) which is NoDup -> impossible unless identical! *)
        clear -Hnd_k H1 H2. induction (eg_line_frags g) as [|[la ka] t IH]; simpl in *; [contradiction|].
        inversion Hnd_k as [|? ? Hna Hndt]; subst.
        destruct H1 as [E1|H1]; destruct H2 as [E2|H2]; try congruence.
        * inversion E1; subst. exfalso. apply Hna.
          replace k1 with (snd (l2, k1)) by reflexivity. apply in_map, H2.
        * inversion E2; subst. exfalso. apply Hna.
          replace k1 with (snd (l1, k1)) by reflexivity. apply in_map, H1.
        * apply IH; assumption.
      + intros [l k] Hlk. apply in_seq. split; [lia|]. exact (proj1 (Hlf l k Hlk)).
      + intros [l k] Hlk. cbn [fst snd]. apply Hline_le; [|exact Hlk].
        assert (Hin_ul : In l ulines) by (unfold ulines; rewrite <- Hmap; change l with (fst (l, k)); apply in_map_iff; exists (l, k); auto).
        apply filter_In in Hin_ul as [Hl _]. exact Hl.
      + exact Hnd_pairs.
      + apply seq_NoDup. }

  assert (Hgain_le : forall i, i < n -> gain reg asg st (nth i embed 0) <= sub_gain frags m_bb b_virt i).
  { intros i Hi. unfold gain, sub_gain.
    set (c := nth i embed 0).
    assert (Hrc : reg c = r) by (apply (Hemb c), nth_In; rewrite Hlen; exact Hi).
    set (ulines := filter (fun l => (asg l =? r) && negb (blocked st0 l)) all_lines).
    transitivity (list_sum (map (fun l => if mem c (frag reg asg l) then weight reg asg st l else 0) ulines)).
    - unfold ulines. clear -Hbincl Hrc.
      induction all_lines as [|l ls IH]; simpl; [lia|].
      destruct (asg l =? r) eqn:Er; destruct (blocked st0 l) eqn:Hb0; simpl.
      + destruct (mem c (frag reg asg l)); [|lia].
        assert (Hw0 : weight reg asg st l = 0).
        { unfold weight. replace (blocked st l) with true; [reflexivity|].
          symmetry. unfold blocked in *. apply existsb_exists in Hb0 as [d [Hd Hdb]].
          apply existsb_exists. exists d. split; [exact Hd|apply mem_spec, Hbincl, mem_spec, Hdb]. }
        rewrite Hw0. lia.
      + destruct (mem c (frag reg asg l)); simpl; lia.
      + destruct (mem c (frag reg asg l)) eqn:Hmc; [|lia].
        exfalso. apply mem_spec, frag_reg in Hmc. apply Nat.eqb_neq in Er. congruence.
      + destruct (mem c (frag reg asg l)) eqn:Hmc; [|lia].
        exfalso. apply mem_spec, frag_reg in Hmc. apply Nat.eqb_neq in Er. congruence.
    - unfold ulines. rewrite <- Hmap, (list_sum_map_nth_seq (fun f => if mem_nat i f then sub_weight m_bb b_virt f else 0) frags []).
      rewrite map_map.
      assert (Hnd_pairs : NoDup (eg_line_frags g)) by (eapply NoDup_map_inv; exact Hnd_k).
      eapply (sum_inj_le snd
                (fun p => if mem c (frag reg asg (fst p)) then weight reg asg st (fst p) else 0)
                (fun k => if mem_nat i (nth k frags []) then sub_weight m_bb b_virt (nth k frags []) else 0)).
      + intros [l1 k1] [l2 k2] H1 H2 Heq. cbn [snd] in Heq. subst k2.
        clear -Hnd_k H1 H2. induction (eg_line_frags g) as [|[la ka] t IH]; simpl in *; [contradiction|].
        inversion Hnd_k as [|? ? Hna Hndt]; subst.
        destruct H1 as [E1|H1]; destruct H2 as [E2|H2]; try congruence.
        * inversion E1; subst. exfalso. apply Hna. replace k1 with (snd (l2, k1)) by reflexivity. apply in_map, H2.
        * inversion E2; subst. exfalso. apply Hna. replace k1 with (snd (l1, k1)) by reflexivity. apply in_map, H1.
        * apply IH; assumption.
      + intros [l k] Hlk. apply in_seq. split; [lia|]. exact (proj1 (Hlf l k Hlk)).
      + intros [l k] Hlk. cbn [fst snd].
        destruct (mem c (frag reg asg l)) eqn:Hmc; [|lia].
        destruct (Hlf l k Hlk) as [Hk Hsame].
        assert (Hfk_in : In (nth k frags []) frags) by (apply nth_In, Hk).
        destruct (Hfr (nth k frags []) Hfk_in) as [_ Hfi].
        assert (Hmi : mem_nat i (nth k frags []) = true).
        { apply mem_nat_spec. apply (map_nth_embed_in_iff embed i (nth k frags []) n Hnd Hlen Hi Hfi).
          apply Hsame, mem_spec, Hmc. }
        rewrite Hmi. apply Hline_le; [|exact Hlk].
        assert (Hin_ul : In l ulines) by (unfold ulines; rewrite <- Hmap; change l with (fst (l, k)); apply in_map_iff; exists (l, k); auto).
        apply filter_In in Hin_ul as [Hl _]. exact Hl.
      + exact Hnd_pairs.
      + apply seq_NoDup. }

  unfold sub_safeb in Hsafe. apply andb_true_iff in Hsafe as [Hsp Hsg].
  apply Nat.ltb_lt in Hsp. rewrite forallb_forall in Hsg.
  split; [lia|].
  intros c Hc125 Hfree Hrc.
  assert (Hcin : In c embed) by (apply Hallc; assumption).
  destruct (In_nth embed c 0 Hcin) as [i [Hi Hci]]. rewrite Hlen in Hi.
  specialize (Hsg i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l _) Hi))).
  assert (Hmi_f : N.testbit m_bb (N.of_nat i) = false).
  { unfold m_bb. rewrite local_mask_bit.
    assert (Hil : (i <? length embed) = true) by (apply Nat.ltb_lt; rewrite Hlen; exact Hi).
    rewrite Hil, Hci. unfold occupied in Hfree. apply orb_false_iff in Hfree as [Hcw _]. exact Hcw. }
  assert (Hbi_f : N.testbit b_virt (N.of_nat i) = false).
  { destruct (N.testbit b_virt (N.of_nat i)) eqn:Eb; [|reflexivity].
    rewrite mask_subb_iff in Hsub. specialize (Hsub _ Eb).
    rewrite local_mask_bit in Hsub.
    assert (Hil : (i <? length embed) = true) by (apply Nat.ltb_lt; rewrite Hlen; exact Hi).
    rewrite Hil, Hci in Hsub. unfold mem in Hsub. unfold occupied in Hfree. apply orb_false_iff in Hfree as [_ Hcb]. congruence. }
  rewrite Hmi_f, Hbi_f in Hsg. simpl in Hsg. apply Nat.ltb_lt in Hsg.
  specialize (Hgain_le i Hi). rewrite Hci in Hgain_le. lia.
Qed.

(** Global hybrid strategy & invariant *)

Definition prev_white_state (st : GameState) : GameState :=
  match white_stones st, history st with
  | _ :: ws, _ :: hs => make_state ws (black_stones st) hs
  | _, _ => st
  end.

Lemma prev_white_add_white st x :
  prev_white_state (add_white st x) = st.
Proof.
  destruct st; reflexivity.
Qed.

Definition hybrid_policy : BlackStrategy :=
  fun st =>
    match history st with
    | [] => 0
    | x :: _ =>
      let r := reg x in
      match find (fun g => eg_reg_id g =? r) gs with
      | Some g =>
          if region_safeb reg asg (prev_white_state st) r
          then best_in_region reg asg st x
          else
            let m_bb := local_mask (white_stones st) (eg_embed g) in
            let b_bb := local_mask (black_stones st) (eg_embed g) in
            match find_shadow_reply (gs_replies (eg_spec g)) m_bb b_bb with
            | Some (_, v) => nth v (eg_embed g) 0
            | None => best_in_region reg asg st x
            end
      | None => best_in_region reg asg st x
      end
    end.

Definition reg_has_gadget (r : nat) : option EmbeddedGadget :=
  find (fun g => eg_reg_id g =? r) gs.

Definition gadget_invariant (st : GameState) (g : EmbeddedGadget) : Prop :=
  region_safe reg asg st (eg_reg_id g) \/
  exists b_virt,
    mask_subb b_virt (local_mask (black_stones st) (eg_embed g)) = true /\
    sub_safe (gs_frags (eg_spec g)) (gs_n (eg_spec g)) (gs_replies (eg_spec g))
             (local_mask (white_stones st) (eg_embed g)) b_virt.

Definition hybrid_invariant (st : GameState) : Prop :=
  valid_state st /\
  incl (black_stones st0) (black_stones st) /\
  (forall g, In g gs -> gadget_compatb reg asg st0 g = true) /\
  NoDup (map eg_reg_id gs) /\
  (forall r, In r (map eg_reg_id gs) ->
     exists g, In g gs /\ eg_reg_id g = r /\ gadget_invariant st g) /\
  (forall r, ~ In r (map eg_reg_id gs) -> region_safe reg asg st r).

Lemma find_gadget_spec r :
  NoDup (map eg_reg_id gs) ->
  match find (fun g => eg_reg_id g =? r) gs with
  | Some g => In g gs /\ eg_reg_id g = r
  | None => ~ In r (map eg_reg_id gs)
  end.
Proof.
  intros Hnd. destruct (find (fun g => eg_reg_id g =? r) gs) as [g|] eqn:Ef.
  - apply find_some in Ef as [Hin Hp]. apply Nat.eqb_eq in Hp. auto.
  - intros Hin. apply in_map_iff in Hin as [g [Hg1 Hg2]].
    apply find_none with (x := g) in Ef; [rewrite Hg1, Nat.eqb_refl in Ef; discriminate|exact Hg2].
Qed.

Lemma find_gadget_unique g :
  NoDup (map eg_reg_id gs) -> In g gs ->
  find (fun g0 => eg_reg_id g0 =? eg_reg_id g) gs = Some g.
Proof.
  intros Hnd Hin. destruct (find (fun g0 => eg_reg_id g0 =? eg_reg_id g) gs) as [g0|] eqn:Ef.
  - apply find_some in Ef as [Hg0 Hp]. apply Nat.eqb_eq in Hp.
    clear -Hnd Hin Hg0 Hp. f_equal.
    induction gs as [|a t IH]; simpl in *; [contradiction|].
    inversion Hnd as [|? ? Hna Hndt]; subst.
    destruct Hin as [<-|Hin]; destruct Hg0 as [<-|Hg0]; try reflexivity.
    + exfalso. apply Hna. rewrite <- Hp. apply in_map, Hg0.
    + exfalso. apply Hna. rewrite Hp. apply in_map, Hin.
    + apply IH; assumption.
  - exfalso. apply find_none with (x := g) in Ef; [rewrite Nat.eqb_refl in Ef; discriminate|exact Hin].
Qed.

Lemma hybrid_no_white_win st :
  hybrid_invariant st -> has_win (white_stones st) = false.
Proof.
  intros [Hvalid [Hbincl [Hcompat [Hnd [Hgs Hother]]]]].
  destruct (has_win (white_stones st)) eqn:Hwin; [|reflexivity].
  exfalso. unfold has_win in Hwin. apply existsb_exists in Hwin as [l [Hl Hline]].
  destruct (in_dec Nat.eq_dec (asg l) (map eg_reg_id gs)) as [Hin|Hnin].
  - destruct (Hgs (asg l) Hin) as [g [Hg1 [Hg2 Hinv]]].
    destruct Hinv as [Hsafe|[b_virt [Hsub Hss]]].
    + destruct Hsafe as [Hp _]. rewrite Hg2 in Hp.
      pose proof (below_32_line_no_white_win reg asg st l Hvalid Hl Hp). congruence.
    + inversion Hss; subst.
      * pose proof (gadget_sub_safeb_to_region_safe g st b_virt (Hcompat g Hg1) Hvalid Hbincl Hsub H) as [Hp _].
        rewrite Hg2 in Hp.
        pose proof (below_32_line_no_white_win reg asg st l Hvalid Hl Hp). congruence.
      * pose proof (gadget_no_white_win reg asg st0 g st l (Hcompat g Hg1) Hvalid Hbincl Hl (eq_sym Hg2) H). congruence.
  - destruct (Hother (asg l) Hnin) as [Hp _].
    pose proof (below_32_line_no_white_win reg asg st l Hvalid Hl Hp). congruence.
Qed.

Lemma hybrid_step_preserves st request :
  hybrid_invariant st -> length (history st) < 125 ->
  let st1 := move_state true st request in
  has_win (white_stones st1) = false /\
  (length (history st1) = 125 -> True) /\
  (length (history st1) < 125 ->
     hybrid_invariant (move_state false st1 (hybrid_policy st1))).
Proof.
  intros Hinv Hlen st1.
  destruct Hinv as [Hvalid [Hbincl [Hcompat [Hnd [Hgs Hother]]]]].
  pose proof (effective_move_is_legal st request Hvalid Hlen) as Hleg.
  destruct (legal_move_fresh st _ Hleg) as [Hxbound [Hxw Hxb]].
  assert (Hxfree : occupied st (effective_move st request) = false)
    by (unfold is_legal_move in Hleg; apply andb_true_iff in Hleg as [_ H]; apply negb_true_iff, H).
  set (x := effective_move st request) in *.
  change st1 with (add_white st x).
  assert (Hvalid1 : valid_state (add_white st x))
    by (apply (move_preserves_validity true st request Hvalid Hlen)).

  assert (Hsafe_white : forall r, region_safe reg asg st r -> phi reg asg (add_white st x) r < 32).
  { intros r [Hp Hg]. rewrite phi_white by exact Hxw.
    destruct (reg x =? r) eqn:Er;
      [apply Nat.eqb_eq in Er; subst r; apply Hg; [exact Hxbound|exact Hxfree|reflexivity]|lia]. }

  assert (Hnowin1 : has_win (white_stones (add_white st x)) = false).
  { destruct (has_win (white_stones (add_white st x))) eqn:Hw1; [|reflexivity].
    exfalso. unfold has_win in Hw1. apply existsb_exists in Hw1 as [l [Hl Hline]].
    destruct (in_dec Nat.eq_dec (asg l) (map eg_reg_id gs)) as [Hin|Hnin].
    - destruct (Hgs (asg l) Hin) as [g [Hg1 [Hg2 Hinvg]]].
      destruct Hinvg as [Hsafe|[b_virt [Hsub Hss]]].
      + rewrite Hg2 in Hsafe.
        assert (Hphi1 : phi reg asg (add_white st x) (asg l) < 32)
          by (apply Hsafe_white, Hsafe).
        pose proof (below_32_line_no_white_win reg asg (add_white st x) l Hvalid1 Hl Hphi1). congruence.
      + inversion Hss; subst.
        * pose proof (gadget_sub_safeb_to_region_safe g st b_virt (Hcompat g Hg1) Hvalid Hbincl Hsub H) as Hsafe.
          rewrite Hg2 in Hsafe.
          assert (Hphi1 : phi reg asg (add_white st x) (asg l) < 32)
            by (apply Hsafe_white, Hsafe).
          pose proof (below_32_line_no_white_win reg asg (add_white st x) l Hvalid1 Hl Hphi1). congruence.
        * pose proof (compat_elim reg asg st0 g (Hcompat g Hg1)) as (_ & Hglen & Hgnd & _).
          assert (Hnw1 : no_frag_win (gs_frags (eg_spec g))
                                     (local_mask (white_stones (add_white st x)) (eg_embed g)) = true).
          { change cell with nat in *.
            replace (white_stones (add_white st x)) with (x :: white_stones st) by (destruct st; reflexivity).
            destruct (in_dec Nat.eq_dec x (eg_embed g)) as [Hxin|Hxnin].
            - destruct (In_nth _ _ 0 Hxin) as [u [Hu Hxu]].
              rewrite (local_mask_add (white_stones st) (eg_embed g) u x Hgnd Hu (eq_sym Hxu)).
              assert (Hmu : N.testbit (local_mask (white_stones st) (eg_embed g)) (N.of_nat u) = false).
              { rewrite local_mask_bit.
                replace (u <? length (eg_embed g)) with true by (symmetry; apply Nat.ltb_lt, Hu).
                replace (nth u (eg_embed g) 0) with x by exact (eq_sym Hxu).
                apply not_true_iff_false. intros Hmem. apply mem_spec in Hmem. contradiction. }
              assert (Hbu : N.testbit b_virt (N.of_nat u) = false).
              { destruct (N.testbit b_virt (N.of_nat u)) eqn:Eb; [|reflexivity].
                rewrite mask_subb_iff in Hsub. specialize (Hsub _ Eb).
                rewrite local_mask_bit in Hsub.
                replace (u <? length (eg_embed g)) with true in Hsub by (symmetry; apply Nat.ltb_lt, Hu).
                replace (nth u (eg_embed g) 0) with x in Hsub by exact (eq_sym Hxu).
                apply mem_spec in Hsub. contradiction. }
              rewrite Hglen in Hu.
              exact (proj1 (H0 u Hu Hmu Hbu)).
            - rewrite local_mask_other by assumption. exact H. }
          pose proof (gadget_no_white_win reg asg st0 g (add_white st x) l
                        (Hcompat g Hg1) Hvalid1 Hbincl Hl (eq_sym Hg2) Hnw1). congruence.
    - pose proof (Hsafe_white (asg l) (Hother (asg l) Hnin)) as Hphi1.
      pose proof (below_32_line_no_white_win reg asg (add_white st x) l Hvalid1 Hl Hphi1). congruence. }

  split; [exact Hnowin1|].
  split; [intro; exact I|].
  intros Hlen1.
  set (req_b := hybrid_policy (add_white st x)).
  set (st2 := move_state false (add_white st x) req_b).
  set (y := effective_move (add_white st x) req_b).
  assert (Hvalid2 : valid_state st2)
    by (apply (move_preserves_validity false (add_white st x) req_b Hvalid1 Hlen1)).
  assert (Hbincl2 : incl (black_stones st0) (black_stones st2)).
  { intros c Hc. unfold st2.
    replace (black_stones (move_state false (add_white st x) req_b))
      with (y :: black_stones st) by (destruct st; reflexivity).
    right. apply Hbincl, Hc. }
  assert (Hother_g : forall r, r <> reg x -> In r (map eg_reg_id gs) ->
            exists g, In g gs /\ eg_reg_id g = r /\ gadget_invariant st2 g).
  { intros r Hne Hr. destruct (Hgs r Hr) as [g [Hg1 [Hg2 Hinvg]]].
    exists g. repeat split; [exact Hg1|exact Hg2|].
    destruct Hinvg as [Hsafe|[b_virt [Hsub Hss]]].
    - left. unfold st2. change (add_white st x) with (move_state true st request).
      apply (region_safe_other_preserved reg asg st request req_b (eg_reg_id g) Hvalid Hlen).
      + exact Hsafe.
      + rewrite Hg2. unfold x in Hne. exact (not_eq_sym Hne).
    - right. exists b_virt. split.
      + eapply mask_subb_trans; [exact Hsub|].
        apply local_mask_incl. intros c Hc. unfold st2.
        replace (black_stones (move_state false (add_white st x) req_b))
          with (y :: black_stones st) by (destruct st; reflexivity).
        right. exact Hc.
      + unfold st2.
        replace (white_stones (move_state false (add_white st x) req_b))
          with (x :: white_stones st) by (destruct st; reflexivity).
        rewrite local_mask_other.
        * exact Hss.
        * pose proof (compat_elim reg asg st0 g (Hcompat g Hg1)) as (_ & _ & _ & Hgemb & _).
          intros Hxin. destruct (Hgemb x Hxin) as [_ [Hrx _]]. congruence. }

  split; [exact Hvalid2|].
  split; [exact Hbincl2|].
  split; [exact Hcompat|].
  split; [exact Hnd|].
  split.
  - intros r Hr.
    destruct (Nat.eq_dec r (reg x)) as [->|Hne]; [|exact (Hother_g r Hne Hr)].
    destruct (Hgs (reg x) Hr) as [g [Hg1 [Hg2 Hinvg]]].
    exists g. repeat split; [exact Hg1|exact Hg2|].
    assert (Hfind : find (fun g0 => eg_reg_id g0 =? reg x) gs = Some g).
    { rewrite <- Hg2. apply find_gadget_unique; assumption. }
    destruct (region_safeb reg asg st (reg x)) eqn:Hrs.
    + left. pose proof (region_safeb_sound _ _ _ _ Hrs) as Hrs_safe.
      assert (Hreq : req_b = best_in_region reg asg (add_white st x) x).
      { unfold req_b, hybrid_policy.
        replace (history (add_white st x)) with (x :: history st) by (destruct st; reflexivity).
        rewrite Hfind, prev_white_add_white, Hrs. reflexivity. }
      unfold st2. rewrite Hreq, Hg2.
      change (add_white st x) with (move_state true st request).
      exact (proj1 (region_safe_reply_preserved reg asg st request Hvalid Hlen Hrs_safe)).
    + assert (Hnot_safe : ~ region_safe reg asg st (reg x)).
      { intros Hs. apply region_safeb_complete in Hs. congruence. }
      destruct Hinvg as [Hsafe|[b_virt [Hsub Hss]]]; [rewrite Hg2 in Hsafe; contradiction|].
      inversion Hss; subst.
      * exfalso. apply Hnot_safe. rewrite <- Hg2.
        exact (gadget_sub_safeb_to_region_safe g st b_virt (Hcompat g Hg1) Hvalid Hbincl Hsub H).
      * pose proof (compat_elim reg asg st0 g (Hcompat g Hg1)) as (Hvg & Hglen & Hgnd & Hgemb & Hgallc & _).
        assert (Hxin : In x (eg_embed g)) by (apply Hgallc; [exact Hxbound|symmetry; exact Hg2]).
        destruct (In_nth _ _ 0 Hxin) as [u [Hu Hxu]].
        assert (Hu_n : u < gs_n (eg_spec g)) by (rewrite <- Hglen; exact Hu).
        assert (Hmu : N.testbit (local_mask (white_stones st) (eg_embed g)) (N.of_nat u) = false).
        { rewrite local_mask_bit.
          replace (u <? length (eg_embed g)) with true by (symmetry; apply Nat.ltb_lt, Hu).
          replace (nth u (eg_embed g) 0) with x by exact (eq_sym Hxu).
          apply not_true_iff_false. intros Hmem. apply mem_spec in Hmem. contradiction. }
        assert (Hbu : N.testbit b_virt (N.of_nat u) = false).
        { destruct (N.testbit b_virt (N.of_nat u)) eqn:Eb; [|reflexivity].
          rewrite mask_subb_iff in Hsub. specialize (Hsub _ Eb).
          rewrite local_mask_bit in Hsub.
          replace (u <? length (eg_embed g)) with true in Hsub by (symmetry; apply Nat.ltb_lt, Hu).
          replace (nth u (eg_embed g) 0) with x in Hsub by exact (eq_sym Hxu).
          apply mem_spec in Hsub. contradiction. }
        destruct (H0 u Hu_n Hmu Hbu) as [_ [v0 [Hass _]]].
        set (m' := N.setbit (local_mask (white_stones st) (eg_embed g)) (N.of_nat u)).
        assert (Hm'_eq : local_mask (white_stones (add_white st x)) (eg_embed g) = m').
        { change cell with nat in *.
          replace (white_stones (add_white st x)) with (x :: white_stones st) by (destruct st; reflexivity).
          apply (local_mask_add (white_stones st) (eg_embed g) u x Hgnd Hu (eq_sym Hxu)). }
        destruct (find_shadow_reply_some _ m' b_virt v0
                    (local_mask (black_stones st) (eg_embed g)) Hass Hsub)
          as [be [v [Hfs [Hin_rep Hsub_be]]]].
        assert (Hreq : req_b = nth v (eg_embed g) 0).
        { unfold req_b, hybrid_policy.
          replace (history (add_white st x)) with (x :: history st) by (destruct st; reflexivity).
          rewrite Hfind, prev_white_add_white, Hrs.
          replace (black_stones (add_white st x)) with (black_stones st) by (destruct st; reflexivity).
          rewrite Hm'_eq, Hfs. reflexivity. }
        destruct (verify_gadgetb_replies _ m' be v Hvg Hin_rep) as (_ & Hv_n & Hmv & Hbv & Hss_next).
        assert (Hv_len : v < length (eg_embed g)) by (rewrite Hglen; exact Hv_n).
        assert (Hy0_lt : nth v (eg_embed g) 0 < 125).
        { assert (Hv_in : In (nth v (eg_embed g) 0) (eg_embed g)) by (apply nth_In, Hv_len).
          destruct (Hgemb (nth v (eg_embed g) 0) Hv_in) as [Hlt _]. exact Hlt. }
        assert (Hy0_nw : ~ In (nth v (eg_embed g) 0) (white_stones (add_white st x))).
        { intros Hin_w.
          assert (Ht : N.testbit (local_mask (white_stones (add_white st x)) (eg_embed g)) (N.of_nat v) = true).
          { rewrite local_mask_bit.
            replace (v <? length (eg_embed g)) with true by (symmetry; apply Nat.ltb_lt, Hv_len).
            apply mem_spec, Hin_w. }
          rewrite Hm'_eq in Ht. congruence. }
        assert (Hy_in_b2 : In (nth v (eg_embed g) 0) (black_stones st2)).
        { destruct (in_dec Nat.eq_dec (nth v (eg_embed g) 0) (black_stones (add_white st x))) as [Hinb|Hninb].
          - unfold st2.
            replace (black_stones (move_state false (add_white st x) req_b))
              with (y :: black_stones st) by (destruct st; reflexivity).
            right. exact Hinb.
          - assert (Hleg_y0 : is_legal_move (add_white st x) (nth v (eg_embed g) 0) = true).
            { unfold is_legal_move. apply andb_true_iff. split; [apply Nat.ltb_lt, Hy0_lt|].
              apply negb_true_iff. unfold occupied. apply orb_false_iff. split;
                apply not_true_iff_false; intros Hmem; apply mem_spec in Hmem; contradiction. }
            unfold st2, y. rewrite Hreq.
            replace (black_stones (move_state false (add_white st x) (nth v (eg_embed g) 0)))
              with (effective_move (add_white st x) (nth v (eg_embed g) 0) :: black_stones (add_white st x))
              by (destruct st; reflexivity).
            rewrite (effective_legal _ _ Hleg_y0). left. reflexivity. }
        right. exists (N.setbit be (N.of_nat v)). split.
        { apply mask_subb_setbit_left.
          - eapply mask_subb_trans; [exact Hsub_be|].
            apply local_mask_incl. intros c Hc. unfold st2.
            replace (black_stones (move_state false (add_white st x) req_b))
              with (y :: black_stones st) by (destruct st; reflexivity).
            right. exact Hc.
          - rewrite local_mask_bit.
            replace (v <? length (eg_embed g)) with true by (symmetry; apply Nat.ltb_lt, Hv_len).
            apply mem_spec, Hy_in_b2. }
        { unfold st2.
          replace (white_stones (move_state false (add_white st x) req_b))
            with (white_stones (add_white st x)) by (destruct st; reflexivity).
          rewrite Hm'_eq. exact Hss_next. }
  - intros r Hr.
    destruct (Nat.eq_dec r (reg x)) as [->|Hne].
    + assert (Hfind : find (fun g0 => eg_reg_id g0 =? reg x) gs = None).
      { destruct (find (fun g0 => eg_reg_id g0 =? reg x) gs) as [g0|] eqn:Ef; [|reflexivity].
        apply find_some in Ef as [Hg0 Hp]. apply Nat.eqb_eq in Hp.
        exfalso. apply Hr. rewrite <- Hp. apply in_map, Hg0. }
      assert (Hreq : req_b = best_in_region reg asg (add_white st x) x).
      { unfold req_b, hybrid_policy.
        replace (history (add_white st x)) with (x :: history st) by (destruct st; reflexivity).
        rewrite Hfind. reflexivity. }
      unfold st2. rewrite Hreq.
      change (add_white st x) with (move_state true st request).
      exact (proj1 (region_safe_reply_preserved reg asg st request Hvalid Hlen (Hother (reg x) Hr))).
    + unfold st2. change (add_white st x) with (move_state true st request).
      apply (region_safe_other_preserved reg asg st request req_b r Hvalid Hlen);
        [apply Hother, Hr|unfold x in Hne; exact (not_eq_sym Hne)].
Qed.

Theorem hybrid_policy_nonloss : forall n st w,
  n + length (history st) = 125 ->
  hybrid_invariant st ->
  outcome (step_game n true st w hybrid_policy) <> WhiteWins.
Proof.
  fix IH 1. intros n st w Hlen Hinv.
  destruct n as [|n]; [cbn [step_game outcome final_result]; discriminate|].
  rewrite step_game_equation. cbn zeta.
  assert (Hhist : length (history st) < 125) by lia.
  destruct (hybrid_step_preserves st (w st) Hinv Hhist) as [Hnw [_ Hstep]].
  set (after_white := move_state true st (w st)) in *.
  assert (Hwlen : length (history after_white) = S (length (history st)))
    by (apply move_state_history).
  unfold move_result at 1. rewrite Hnw.
  destruct (length (history after_white) =? 125) eqn:Hfull; [discriminate|].
  apply Nat.eqb_neq in Hfull.
  destruct n as [|n]; [exfalso; apply Hfull; lia|].
  rewrite step_game_equation. cbn zeta.
  change (outcome
    (let next := move_state false after_white (hybrid_policy after_white) in
     match move_result false next with
     | Some r => make_trace next r
     | None => step_game n true next w hybrid_policy
     end) <> WhiteWins).
  set (after_black := move_state false after_white (hybrid_policy after_white)) in *.
  cbv zeta.
  assert (Hblen : length (history after_black) = S (length (history after_white)))
    by (apply move_state_history).
  assert (Hlt1 : length (history after_white) < 125) by lia.
  specialize (Hstep Hlt1).
  change (move_state false after_white (hybrid_policy after_white)) with after_black in Hstep.
  unfold move_result.
  destruct (has_win (black_stones after_black)); [discriminate|].
  destruct (length (history after_black) =? 125); [discriminate|].
  apply (IH n after_black w); [lia|exact Hstep].
Qed.

End HybridSoundness2.

Lemma region_safe_unused reg asg st r :
  ~ In r (map asg all_lines) ->
  region_safe reg asg st r.
Proof.
  intros Hr. split.
  - unfold phi. rewrite (sum_map_const _ 0); [lia|].
    intros l Hl. destruct (asg l =? r) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. exfalso. apply Hr. rewrite <- E. apply in_map, Hl.
  - intros c Hc Hfree Hrc.
    replace (phi reg asg st r) with 0.
    + replace (gain reg asg st c) with 0; [lia|].
      unfold gain. symmetry. apply (sum_map_const _ 0). intros l Hl.
      destruct (mem c (frag reg asg l)) eqn:Hm; [|reflexivity].
      apply mem_spec, frag_reg in Hm. exfalso. apply Hr. rewrite <- Hrc, Hm. apply in_map, Hl.
    + unfold phi. symmetry. apply (sum_map_const _ 0).
      intros l Hl. destruct (asg l =? r) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso. apply Hr. rewrite <- E. apply in_map, Hl.
Qed.

Fixpoint dedup_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if mem_nat x xs then dedup_nat xs else x :: dedup_nat xs
  end.

Lemma dedup_nat_in x l : In x (dedup_nat l) <-> In x l.
Proof.
  induction l as [|y ys IH]; simpl; [tauto|].
  destruct (mem_nat y ys) eqn:Hm.
  - apply mem_nat_spec in Hm. rewrite IH. split; [intro H; right; exact H|].
    intros [<-|H]; assumption.
  - simpl. rewrite IH. tauto.
Qed.

Definition region_entry := (nat * (list cell * nat))%type.

Definition mk_entries (reg : cell -> nat) (asg : list cell -> nat) (st : GameState) : list region_entry :=
  map (fun l => (asg l, (frag reg asg l, weight reg asg st l))) all_lines.

Definition phi_of (entries : list region_entry) (r : nat) : nat :=
  list_sum (map (fun '(rl, (_, w)) => if rl =? r then w else 0) entries).

Definition gain_of (entries : list region_entry) (x : cell) : nat :=
  list_sum (map (fun '(_, (fr, w)) => if mem x fr then w else 0) entries).

Lemma phi_of_entries reg asg st r :
  phi_of (mk_entries reg asg st) r = phi reg asg st r.
Proof.
  unfold phi_of, phi, mk_entries. rewrite map_map. reflexivity.
Qed.

Lemma gain_of_entries reg asg st x :
  gain_of (mk_entries reg asg st) x = gain reg asg st x.
Proof.
  unfold gain_of, gain, mk_entries. rewrite map_map. reflexivity.
Qed.

Definition hybrid_certificateb (reg : cell -> nat) (asg : list cell -> nat)
    (gs : list EmbeddedGadget) (st0 : GameState) : bool :=
  let gids := map eg_reg_id gs in
  let entries := mk_entries reg asg st0 in
  let regs := dedup_nat (filter (fun r => negb (mem_nat r gids)) (map fst entries)) in
  nodupb Nat.eqb gids &&
  forallb (gadget_compatb reg asg st0) gs &&
  forallb (fun r => phi_of entries r <? 32) regs &&
  forallb (fun c => if occupied st0 c then true
                    else let rc := reg c in
                         mem_nat rc gids || (phi_of entries rc + gain_of entries c <? 32))
          all_cells.

Theorem hybrid_certificate_invariant reg asg gs st0 :
  valid_state st0 ->
  hybrid_certificateb reg asg gs st0 = true ->
  hybrid_invariant reg asg st0 gs st0.
Proof.
  intros Hvalid Hcert.
  unfold hybrid_certificateb in Hcert.
  apply andb_true_iff in Hcert as [H123 Hcells_b].
  apply andb_true_iff in H123 as [H12 Hregs_b].
  apply andb_true_iff in H12 as [Hnd_b Hcompat_b].
  apply nat_nodupb_sound in Hnd_b.
  rewrite forallb_forall in Hcompat_b.
  rewrite forallb_forall in Hregs_b.
  rewrite forallb_forall in Hcells_b.
  split; [exact Hvalid|].
  split; [intros c Hc; exact Hc|].
  split; [exact Hcompat_b|].
  split; [exact Hnd_b|].
  split.
  - intros r Hr. apply in_map_iff in Hr as [g [Hg1 Hg2]].
    exists g. repeat split; [exact Hg2|exact Hg1|].
    right. exists 0%N.
    pose proof (compat_elim reg asg st0 g (Hcompat_b g Hg2)) as (Hvg & _ & _ & Hgemb & _).
    assert (Hm0 : local_mask (white_stones st0) (eg_embed g) = 0%N).
    { apply local_mask_all_false. rewrite Forall_forall. intros c Hc.
      destruct (Hgemb c Hc) as [_ [_ Hfree]].
      unfold occupied, mem in Hfree. apply orb_false_iff in Hfree as [Hw _]. exact Hw. }
    assert (Hb0 : local_mask (black_stones st0) (eg_embed g) = 0%N).
    { apply local_mask_all_false. rewrite Forall_forall. intros c Hc.
      destruct (Hgemb c Hc) as [_ [_ Hfree]].
      unfold occupied, mem in Hfree. apply orb_false_iff in Hfree as [_ Hb]. exact Hb. }
    split; [apply mask_subb_0|].
    rewrite Hm0. apply verify_gadgetb_sound, Hvg.
  - intros r Hr. destruct (in_dec Nat.eq_dec r (map asg all_lines)) as [Hin|Hnin].
    + assert (Hin_r : In r (dedup_nat (filter (fun r0 => negb (mem_nat r0 (map eg_reg_id gs))) (map fst (mk_entries reg asg st0))))).
      { apply dedup_nat_in, filter_In. split.
        - unfold mk_entries. rewrite map_map. exact Hin.
        - apply negb_true_iff. destruct (mem_nat r (map eg_reg_id gs)) eqn:Hm; [apply mem_nat_spec in Hm; contradiction|reflexivity]. }
      split.
      * specialize (Hregs_b r Hin_r). rewrite phi_of_entries in Hregs_b. apply Nat.ltb_lt, Hregs_b.
      * intros c Hc Hfree Hrc.
        specialize (Hcells_b c (proj2 (all_cells_spec c) Hc)).
        rewrite Hfree, Hrc in Hcells_b.
        apply orb_true_iff in Hcells_b as [Hm|Hlt].
        { apply mem_nat_spec in Hm. contradiction. }
        { rewrite phi_of_entries, gain_of_entries in Hlt. apply Nat.ltb_lt, Hlt. }
    + apply region_safe_unused, Hnin.
Qed.

Theorem hybrid_certificate_nonloss : forall reg asg gs st0 n w,
  valid_state st0 ->
  n + length (history st0) = 125 ->
  hybrid_certificateb reg asg gs st0 = true ->
  outcome (step_game n true st0 w (hybrid_policy reg asg gs)) <> WhiteWins.
Proof.
  intros reg asg gs st0 n w Hvalid Hlen Hcert.
  apply (hybrid_policy_nonloss reg asg st0 gs n st0 w Hlen).
  apply (hybrid_certificate_invariant reg asg gs st0 Hvalid Hcert).
Qed.

Print Assumptions hybrid_certificate_nonloss.
