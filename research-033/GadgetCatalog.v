(** Verified Gadget Catalog for 5x5x5 Qubic:
    - Depth-0 K_4 Veblen gadget (`sub_safeb = true`, `sub_phi = 16`)
    - Constructive proof that NO partition of K_4 achieves Erdős-Selfridge
      potential < 16 (`Phi < 0.5`), demonstrating exact separation vs Layer 4.3
    - Bounded adaptive bottom-up DAGs for `K_{3,3}`, `S_{10}`, `3R+3C+2D`,
      `4R+4C`, and `Slice-14`, all kernel-verified via `verify_gadgetb ... = true`. *)

From Stdlib Require Import List Arith Bool Lia NArith.
From QubicTrusted Require Import Rules.
From QubicAgent Require Import RulesFacts.
From QubicResearch033 Require Import ExactRegionCertificates.
Import ListNotations.

(** ** 1. Veblen K_4 Gadget and Layer-4 (< 16) vs Layer-4.3 (phi + gain < 32) Separation *)

Definition frags_K4 : list (list nat) :=
  [[0; 1; 2]; [0; 3; 4]; [1; 3; 5]; [2; 4; 5]].

Definition gadget_K4 : GadgetSpec :=
  mk_gadget_spec 6 frags_K4 [] [].

Theorem K4_sub_safeb : sub_safeb 6 frags_K4 0%N 0%N = true.
Proof. vm_compute. reflexivity. Qed.

Theorem K4_sub_phi_16 : sub_phi frags_K4 0%N 0%N = 16.
Proof. vm_compute. reflexivity. Qed.

Theorem K4_verified : verify_gadgetb gadget_K4 = true.
Proof. vm_compute. reflexivity. Qed.

Definition k4_frag (reg : nat -> nat) (asg : list nat -> nat) (f : list nat) : list nat :=
  filter (fun i => reg i =? asg f) f.

Definition k4_weight (reg : nat -> nat) (asg : list nat -> nat) (f : list nat) : nat :=
  2 ^ (5 - length (k4_frag reg asg f)).

Definition k4_phi (reg : nat -> nat) (asg : list nat -> nat) (r : nat) : nat :=
  list_sum (map (fun f => if asg f =? r then k4_weight reg asg f else 0) frags_K4).

Definition mask_ge2_count (s : N) : nat :=
  length (filter (fun f => 2 <=? length (filter (fun i => N.testbit s (N.of_nat i)) f)) frags_K4).

Definition mask_ge2_sum (s : N) : nat :=
  list_sum (map (fun f =>
    let k := length (filter (fun i => N.testbit s (N.of_nat i)) f) in
    if 2 <=? k then 2 ^ (5 - k) else 0) frags_K4).

Lemma k4_mask_64_check :
  forallb (fun sn =>
    let s := N.of_nat sn in
    if mask_ge2_count s <? 2 then true else 16 <=? mask_ge2_sum s) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frags_K4_props :
  forallb (fun f => nodupb Nat.eqb f && (length f =? 3) && forallb (fun i => i <? 6) f) frags_K4 = true.
Proof. vm_compute. reflexivity. Qed.

Fixpoint mask_pred (p : nat -> bool) (n : nat) : N :=
  match n with
  | 0 => 0%N
  | S k => if p k then N.setbit (mask_pred p k) (N.of_nat k) else mask_pred p k
  end.

Lemma mask_pred_upper p n j :
  N.testbit (mask_pred p n) (N.of_nat j) = true -> j < n.
Proof.
  induction n as [|k IH]; simpl; [discriminate|].
  destruct (p k).
  - destruct (Nat.eq_dec j k) as [->|Hne]; [lia|].
    rewrite N.setbit_neq by lia. intros H. apply IH in H. lia.
  - intros H. apply IH in H. lia.
Qed.

Lemma mask_pred_testbit p n j :
  j < n -> N.testbit (mask_pred p n) (N.of_nat j) = p j.
Proof.
  induction n as [|k IH]; [lia|].
  simpl. intros Hj. destruct (Nat.eq_dec j k) as [->|Hne].
  - destruct (p k) eqn:E.
    + rewrite N.setbit_eq. reflexivity.
    + destruct (N.testbit (mask_pred p k) (N.of_nat k)) eqn:Et; [|reflexivity].
      apply mask_pred_upper in Et. lia.
  - destruct (p k); [rewrite N.setbit_neq by lia|]; apply IH; lia.
Qed.

Lemma n_bits_bound_pow2 b m :
  (forall j, N.testbit b (N.of_nat j) = true -> j < m) -> N.to_nat b < 2 ^ m.
Proof.
  revert b. induction m as [|m IHm]; intros b Hb.
  - replace b with 0%N; [simpl; lia|].
    apply N.bits_inj. intros k. rewrite N.bits_0.
    destruct (N.testbit b k) eqn:Eb; [|reflexivity].
    rewrite <- (N2Nat.id k) in Eb. apply Hb in Eb. lia.
  - specialize (IHm (N.div2 b)).
    assert (Hdiv : forall j, N.testbit (N.div2 b) (N.of_nat j) = true -> j < m).
    { intros j Hj. rewrite N.div2_spec, N.shiftr_spec in Hj by lia.
      replace (N.of_nat j + 1)%N with (N.of_nat (S j)) in Hj by lia.
      apply Hb in Hj. lia. }
    specialize (IHm Hdiv).
    pose proof (N.div_mod b 2 ltac:(discriminate)) as Hdm.
    assert (Hmod : (b mod 2 < 2)%N) by (apply N.mod_lt; discriminate).
    rewrite Nat.pow_succ_r'. rewrite Hdm at 1.
    rewrite <- N.div2_div.
    rewrite N2Nat.inj_add, N2Nat.inj_mul.
    assert (Hm2 : N.to_nat (b mod 2) < 2) by lia.
    simpl (N.to_nat 2). lia.
Qed.

Lemma disjoint_filter_sum reg (rs xs : list nat) :
  NoDup rs ->
  list_sum (map (fun r => length (filter (fun i => reg i =? r) xs)) rs) <= length xs.
Proof.
  induction xs as [|a t IH]; intros Hnd; simpl.
  - rewrite (sum_map_const _ 0); [lia|intros; reflexivity].
  - transitivity (list_sum (map (fun r => (if reg a =? r then 1 else 0) +
                                          length (filter (fun i => reg i =? r) t)) rs)).
    + apply Nat.eq_le_incl, sum_map_ext_in. intros r _.
      destruct (reg a =? r); simpl; lia.
    + rewrite sum_map_add.
      assert (Hhit : list_sum (map (fun r => if reg a =? r then 1 else 0) rs) <= 1).
      { clear IH. induction rs as [|r rs' IHrs]; simpl; [lia|].
        inversion Hnd as [|? ? Hna Hndt]; subst.
        destruct (reg a =? r) eqn:E.
        - apply Nat.eqb_eq in E. rewrite <- E in Hna.
          rewrite (sum_map_const (fun r0 => if reg a =? r0 then 1 else 0) 0).
          + lia.
          + intros r0 Hr0. destruct (reg a =? r0) eqn:E0; [apply Nat.eqb_eq in E0; subst; contradiction|reflexivity].
        - simpl. apply IHrs, Hndt. }
      pose proof (IH Hnd). lia.
Qed.

Lemma filter_sum_split {A} (p1 p2 : A -> bool) l :
  (forall x, In x l -> p1 x = true -> p2 x = false) ->
  length (filter p1 l) + length (filter p2 l) <= length l.
Proof.
  induction l as [|a t IH]; simpl; intros H; [lia|].
  assert (Ht : length (filter p1 t) + length (filter p2 t) <= length t)
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (p1 a) eqn:E1.
  - rewrite (H a (or_introl eq_refl) E1). simpl. lia.
  - destruct (p2 a); simpl; lia.
Qed.

Lemma nodup_nat_dup (xs : list nat) :
  nodupb Nat.eqb xs = false ->
  exists r, 2 <= length (filter (fun y => y =? r) xs).
Proof.
  induction xs as [|x xs' IH]; simpl; [discriminate|].
  destruct (existsb (Nat.eqb x) xs') eqn:E.
  - intros _. exists x. rewrite Nat.eqb_refl. simpl.
    apply existsb_exists in E as [y [Hy Heq]]. apply Nat.eqb_eq in Heq. subst y.
    clear -Hy. induction xs' as [|a t IHx]; simpl in *; [contradiction|].
    destruct Hy as [<-|Hy]; [rewrite Nat.eqb_refl; simpl; lia|].
    destruct (a =? x); simpl; [pose proof (IHx Hy); lia|apply IHx, Hy].
  - simpl. intros H. destruct (IH H) as [r Hr]. exists r.
    destruct (x =? r); simpl; lia.
Qed.

Lemma length_filter_map_count {A} (g : A -> nat) l r :
  length (filter (fun y => y =? r) (map g l)) =
  length (filter (fun x => g x =? r) l).
Proof.
  induction l as [|a t IH]; simpl; [reflexivity|].
  destruct (g a =? r); simpl; lia.
Qed.

Theorem K4_no_es_lt16_partition : forall (reg : nat -> nat) (asg : list nat -> nat),
  exists r, 16 <= k4_phi reg asg r.
Proof.
  intros reg asg.
  destruct (find (fun f => 16 <=? k4_phi reg asg (asg f)) frags_K4) as [f0|] eqn:Ef.
  { apply find_some in Ef as [_ Hge]. apply Nat.leb_le in Hge. exists (asg f0). exact Hge. }
  exfalso.
  assert (Hlt : forall f, In f frags_K4 -> k4_phi reg asg (asg f) < 16).
  { intros f Hf. apply find_none with (x := f) in Ef; [apply Nat.leb_gt in Ef; exact Ef|exact Hf]. }
  assert (Hge2 : forall f, In f frags_K4 -> 2 <= length (k4_frag reg asg f)).
  { intros f Hf.
    assert (Hwf : k4_weight reg asg f <= k4_phi reg asg (asg f)).
    { unfold k4_phi.
      pose proof (sum_map_term (fun f0 => if asg f0 =? asg f then k4_weight reg asg f0 else 0) frags_K4 f Hf) as Ht.
      cbn beta in Ht. rewrite Nat.eqb_refl in Ht. exact Ht. }
    pose proof (Hlt f Hf). unfold k4_weight in Hwf.
    destruct (length (k4_frag reg asg f)) as [|[|k]]; [simpl in Hwf; lia|simpl in Hwf; lia|lia]. }
  assert (Hfk_prop : forall f, In f frags_K4 -> NoDup f /\ length f = 3 /\ forall i, In i f -> i < 6).
  { intros f Hf. pose proof frags_K4_props as Hp. rewrite forallb_forall in Hp.
    specialize (Hp f Hf). apply andb_true_iff in Hp as [Hp Hi].
    apply andb_true_iff in Hp as [Hnd Hl]. split; [apply nat_nodupb_sound, Hnd|].
    split; [apply Nat.eqb_eq, Hl|intros i Hif; rewrite forallb_forall in Hi; apply Nat.ltb_lt, Hi, Hif]. }
  destruct (nodupb Nat.eqb (map asg frags_K4)) eqn:End.
  - apply nat_nodupb_sound in End.
    pose proof (disjoint_filter_sum reg (map asg frags_K4) (seq 0 6) End) as Hsum.
    rewrite length_seq in Hsum.
    assert (H8 : 8 <= list_sum (map (fun r => length (filter (fun i => reg i =? r) (seq 0 6))) (map asg frags_K4))).
    { rewrite map_map.
      transitivity (list_sum (map (fun _ : list nat => 2) frags_K4)).
      - simpl. lia.
      - apply sum_map_le. intros f Hf.
        destruct (Hfk_prop f Hf) as [Hndf [_ Hfi]].
        transitivity (length (k4_frag reg asg f)); [apply Hge2, Hf|].
        apply NoDup_incl_length; [apply NoDup_filter, Hndf|].
        intros i Hi. apply filter_In in Hi as [Hif Hir].
        apply filter_In. split; [apply in_seq; split; [lia|apply Hfi, Hif]|exact Hir]. }
    lia.
  - apply nodup_nat_dup in End as [r Hr].
    rewrite length_filter_map_count in Hr.
    set (s := mask_pred (fun i => reg i =? r) 6).
    assert (Hs64 : N.to_nat s < 64).
    { apply (n_bits_bound_pow2 s 6). intros j Hj. apply mask_pred_upper in Hj. exact Hj. }
    pose proof k4_mask_64_check as Hchk. rewrite forallb_forall in Hchk.
    specialize (Hchk (N.to_nat s) (proj2 (in_seq _ _ _) (conj (Nat.le_0_l _) Hs64))).
    cbn zeta in Hchk. rewrite N2Nat.id in Hchk.
    assert (Hfilt_eq : forall f, In f frags_K4 ->
              (2 <=? length (filter (fun i => N.testbit s (N.of_nat i)) f)) = (asg f =? r)).
    { intros f Hf. destruct (Hfk_prop f Hf) as [_ [Hlf Hfi]].
      destruct (asg f =? r) eqn:Er.
      - apply Nat.eqb_eq in Er. apply Nat.leb_le.
        replace (length (filter (fun i => N.testbit s (N.of_nat i)) f))
          with (length (k4_frag reg asg f)); [apply Hge2, Hf|].
        unfold k4_frag. f_equal. apply filter_ext_in. intros i Hi.
        unfold s. rewrite Er, mask_pred_testbit by (apply Hfi, Hi). reflexivity.
      - apply Nat.leb_gt.
        pose proof (filter_sum_split (fun i => N.testbit s (N.of_nat i)) (fun i => reg i =? asg f) f) as Hsp.
        assert (Hdisj : forall i, In i f -> N.testbit s (N.of_nat i) = true -> (reg i =? asg f) = false).
        { intros i Hif Htb. unfold s in Htb. rewrite mask_pred_testbit in Htb by (apply Hfi, Hif).
          apply Nat.eqb_eq in Htb. apply Nat.eqb_neq in Er. apply Nat.eqb_neq. congruence. }
        specialize (Hsp Hdisj). fold (k4_frag reg asg f) in Hsp.
        pose proof (Hge2 f Hf). lia. }
    assert (Hcnt : 2 <= mask_ge2_count s).
    { unfold mask_ge2_count.
      replace (filter (fun f => 2 <=? length (filter (fun i => N.testbit s (N.of_nat i)) f)) frags_K4)
        with (filter (fun f => asg f =? r) frags_K4); [exact Hr|].
      apply filter_ext_in. intros f Hf. symmetry. apply Hfilt_eq, Hf. }
    assert (Hcnt_lt : (mask_ge2_count s <? 2) = false) by (apply Nat.ltb_ge, Hcnt).
    rewrite Hcnt_lt in Hchk. apply Nat.leb_le in Hchk.
    assert (Hphi_eq : mask_ge2_sum s = k4_phi reg asg r).
    { unfold mask_ge2_sum, k4_phi. apply sum_map_ext_in. intros f Hf.
      rewrite Hfilt_eq by exact Hf. destruct (asg f =? r) eqn:Er; [|reflexivity].
      apply Nat.eqb_eq in Er. destruct (Hfk_prop f Hf) as [_ [_ Hfi]].
      unfold k4_weight, k4_frag. f_equal. f_equal. f_equal.
      apply filter_ext_in. intros i Hi. unfold s. rewrite Er, mask_pred_testbit by (apply Hfi, Hi). reflexivity. }
    rewrite Hphi_eq in Hchk.
    assert (Hr_in : In r (map asg frags_K4)).
    { destruct (filter (fun f => asg f =? r) frags_K4) as [|f1 ft] eqn:Ef1; [simpl in Hr; lia|].
      assert (Hin : In f1 (filter (fun f => asg f =? r) frags_K4)) by (rewrite Ef1; left; reflexivity).
      apply filter_In in Hin as [Hf1 Er1]. apply Nat.eqb_eq in Er1. rewrite <- Er1. apply in_map, Hf1. }
    apply in_map_iff in Hr_in as [f1 [Er1 Hf1]]. rewrite <- Er1 in Hchk.
    pose proof (Hlt f1 Hf1). lia.
Qed.


(** ** 2. Verified Adaptive Gadget Catalog (`K_{3,3}`, `S_{10}`, `3R+3C+2D`, `4R+4C`, `Slice-14`) *)

Definition gadget_K33 : GadgetSpec := mk_gadget_spec
  9
  [ [0; 1; 2]; [3; 4; 5]; [6; 7; 8]; [0; 3; 6]; [1; 4; 7]; [2; 5; 8] ]
  [
  (1%N, 2%N); (2%N, 1%N); (4%N, 1%N); (8%N, 1%N); (16%N, 2%N);
  (32%N, 4%N); (64%N, 1%N); (128%N, 2%N); (256%N, 4%N); (0%N, 0%N)
]
  [
  ((1%N, 0%N), 1); ((2%N, 0%N), 0); ((4%N, 0%N), 0); ((5%N, 2%N), 3);
  ((6%N, 1%N), 4); ((8%N, 0%N), 0); ((9%N, 2%N), 6); ((10%N, 1%N), 4);
  ((12%N, 1%N), 4); ((16%N, 0%N), 1); ((17%N, 2%N), 3); ((18%N, 1%N), 7);
  ((20%N, 1%N), 5); ((20%N, 2%N), 3); ((24%N, 1%N), 5); ((24%N, 2%N), 5);
  ((32%N, 0%N), 2); ((33%N, 2%N), 3); ((33%N, 4%N), 3); ((34%N, 1%N), 4);
  ((34%N, 4%N), 3); ((36%N, 1%N), 8); ((40%N, 1%N), 4); ((40%N, 4%N), 4);
  ((48%N, 2%N), 3); ((48%N, 4%N), 3); ((64%N, 0%N), 0); ((65%N, 2%N), 3);
  ((66%N, 1%N), 4); ((68%N, 1%N), 5); ((72%N, 1%N), 4); ((80%N, 1%N), 7);
  ((80%N, 2%N), 3); ((96%N, 1%N), 7); ((96%N, 4%N), 3); ((128%N, 0%N), 1);
  ((129%N, 2%N), 3); ((130%N, 1%N), 4); ((132%N, 1%N), 5); ((132%N, 2%N), 5);
  ((136%N, 1%N), 4); ((136%N, 2%N), 6); ((144%N, 2%N), 3); ((160%N, 2%N), 6);
  ((160%N, 4%N), 3); ((192%N, 1%N), 8); ((192%N, 2%N), 8); ((256%N, 0%N), 2);
  ((257%N, 2%N), 3); ((257%N, 4%N), 3); ((258%N, 1%N), 4); ((258%N, 4%N), 4);
  ((260%N, 1%N), 5); ((264%N, 1%N), 4); ((264%N, 4%N), 6); ((272%N, 2%N), 3);
  ((272%N, 4%N), 6); ((288%N, 4%N), 3); ((320%N, 1%N), 7); ((320%N, 4%N), 7);
  ((384%N, 2%N), 6); ((384%N, 4%N), 6)
].

Theorem K33_verified : verify_gadgetb gadget_K33 = true.
Proof. vm_compute. reflexivity. Qed.

Definition gadget_S10 : GadgetSpec := mk_gadget_spec
  10
  [ [0; 1; 2]; [3; 4; 5]; [7; 8; 9]; [0; 3; 7]; [1; 4; 8]; [2; 5; 9]; [0; 4; 6; 9] ]
  [
  (17%N, 10%N); (33%N, 10%N); (48%N, 10%N); (129%N, 10%N); (144%N, 10%N);
  (513%N, 10%N); (513%N, 132%N); (520%N, 132%N); (528%N, 10%N); (528%N, 132%N);
  (768%N, 132%N); (1%N, 2%N); (2%N, 1%N); (4%N, 1%N); (8%N, 1%N);
  (16%N, 2%N); (32%N, 16%N); (128%N, 1%N); (256%N, 16%N); (512%N, 4%N);
  (0%N, 0%N)
]
  [
  ((1%N, 0%N), 1); ((2%N, 0%N), 0); ((4%N, 0%N), 0); ((5%N, 2%N), 9);
  ((6%N, 1%N), 4); ((8%N, 0%N), 0); ((9%N, 2%N), 7); ((10%N, 1%N), 4);
  ((12%N, 1%N), 4); ((16%N, 0%N), 1); ((17%N, 2%N), 3); ((18%N, 1%N), 8);
  ((20%N, 1%N), 5); ((20%N, 2%N), 9); ((21%N, 10%N), 9); ((24%N, 1%N), 5);
  ((24%N, 2%N), 5); ((32%N, 0%N), 4); ((33%N, 2%N), 3); ((33%N, 16%N), 2);
  ((34%N, 1%N), 4); ((34%N, 16%N), 0); ((36%N, 1%N), 9); ((36%N, 16%N), 9);
  ((37%N, 10%N), 9); ((40%N, 1%N), 4); ((40%N, 16%N), 0); ((48%N, 2%N), 3);
  ((49%N, 10%N), 9); ((52%N, 10%N), 9); ((64%N, 0%N), 0); ((65%N, 2%N), 9);
  ((66%N, 1%N), 4); ((68%N, 1%N), 4); ((72%N, 1%N), 4); ((80%N, 2%N), 9);
  ((81%N, 10%N), 9); ((96%N, 16%N), 0); ((97%N, 10%N), 9); ((112%N, 10%N), 9);
  ((128%N, 0%N), 0); ((129%N, 2%N), 3); ((130%N, 1%N), 4); ((132%N, 1%N), 5);
  ((133%N, 10%N), 9); ((136%N, 1%N), 4); ((144%N, 1%N), 8); ((144%N, 2%N), 3);
  ((145%N, 10%N), 9); ((148%N, 10%N), 9); ((160%N, 1%N), 8); ((160%N, 16%N), 2);
  ((161%N, 10%N), 9); ((176%N, 10%N), 9); ((192%N, 1%N), 4); ((193%N, 10%N), 9);
  ((208%N, 10%N), 9); ((256%N, 0%N), 4); ((257%N, 2%N), 9); ((257%N, 16%N), 7);
  ((258%N, 1%N), 4); ((258%N, 16%N), 0); ((260%N, 1%N), 5); ((260%N, 16%N), 7);
  ((264%N, 1%N), 4); ((264%N, 16%N), 0); ((272%N, 2%N), 9); ((273%N, 10%N), 9);
  ((288%N, 16%N), 2); ((289%N, 10%N), 9); ((304%N, 10%N), 9); ((320%N, 16%N), 0);
  ((384%N, 1%N), 9); ((384%N, 16%N), 9); ((385%N, 10%N), 9); ((400%N, 10%N), 9);
  ((512%N, 0%N), 2); ((513%N, 2%N), 3); ((513%N, 4%N), 7); ((514%N, 1%N), 4);
  ((514%N, 4%N), 4); ((515%N, 132%N), 4); ((516%N, 1%N), 5); ((517%N, 10%N), 5);
  ((520%N, 1%N), 4); ((520%N, 4%N), 7); ((521%N, 132%N), 4); ((522%N, 132%N), 4);
  ((528%N, 2%N), 3); ((528%N, 4%N), 7); ((529%N, 10%N), 6); ((529%N, 132%N), 6);
  ((530%N, 132%N), 8); ((532%N, 10%N), 5); ((536%N, 132%N), 5); ((544%N, 4%N), 4);
  ((544%N, 16%N), 2); ((545%N, 10%N), 2); ((545%N, 132%N), 4); ((552%N, 132%N), 4);
  ((560%N, 10%N), 2); ((560%N, 132%N), 3); ((576%N, 4%N), 4); ((577%N, 10%N), 4);
  ((577%N, 132%N), 4); ((584%N, 132%N), 4); ((592%N, 10%N), 0); ((592%N, 132%N), 0);
  ((640%N, 1%N), 8); ((640%N, 4%N), 8); ((641%N, 10%N), 8); ((656%N, 10%N), 8);
  ((768%N, 4%N), 7); ((768%N, 16%N), 7); ((769%N, 10%N), 7); ((769%N, 132%N), 4);
  ((770%N, 132%N), 4); ((776%N, 132%N), 4); ((784%N, 10%N), 7); ((784%N, 132%N), 1);
  ((800%N, 132%N), 4); ((832%N, 132%N), 4)
].

Theorem S10_verified : verify_gadgetb gadget_S10 = true.
Proof. vm_compute. reflexivity. Qed.

Definition gadget_3R3C2D : GadgetSpec := mk_gadget_spec
  12
  [ [0; 1; 2]; [3; 4; 5]; [7; 8; 9]; [0; 3; 7]; [1; 4; 8]; [2; 5; 9]; [0; 4; 6; 9; 11]; [5; 6; 8; 10] ]
  [
  (33%N, 10%N); (513%N, 10%N); (1%N, 2%N); (2%N, 1%N); (4%N, 1%N);
  (8%N, 1%N); (16%N, 32%N); (32%N, 16%N); (128%N, 1%N); (256%N, 16%N);
  (512%N, 32%N); (0%N, 0%N)
]
  [
  ((1%N, 0%N), 1); ((2%N, 0%N), 0); ((4%N, 0%N), 0); ((5%N, 2%N), 5);
  ((6%N, 1%N), 5); ((8%N, 0%N), 0); ((9%N, 2%N), 7); ((10%N, 1%N), 5);
  ((12%N, 1%N), 5); ((16%N, 0%N), 5); ((17%N, 2%N), 5); ((17%N, 32%N), 1);
  ((18%N, 1%N), 8); ((18%N, 32%N), 8); ((20%N, 1%N), 5); ((20%N, 32%N), 0);
  ((24%N, 1%N), 5); ((24%N, 32%N), 0); ((32%N, 0%N), 4); ((33%N, 2%N), 3);
  ((33%N, 16%N), 2); ((34%N, 1%N), 8); ((34%N, 16%N), 0); ((36%N, 1%N), 9);
  ((36%N, 16%N), 9); ((37%N, 10%N), 9); ((40%N, 1%N), 4); ((40%N, 16%N), 0);
  ((49%N, 10%N), 9); ((64%N, 0%N), 4); ((65%N, 2%N), 5); ((66%N, 1%N), 5);
  ((68%N, 1%N), 5); ((72%N, 1%N), 5); ((80%N, 32%N), 0); ((96%N, 16%N), 2);
  ((97%N, 10%N), 9); ((128%N, 0%N), 0); ((129%N, 2%N), 3); ((130%N, 1%N), 8);
  ((132%N, 1%N), 5); ((136%N, 1%N), 5); ((144%N, 1%N), 8); ((144%N, 32%N), 1);
  ((160%N, 1%N), 8); ((160%N, 16%N), 9); ((161%N, 10%N), 9); ((192%N, 1%N), 5);
  ((256%N, 0%N), 4); ((257%N, 2%N), 9); ((257%N, 16%N), 7); ((258%N, 1%N), 4);
  ((258%N, 16%N), 0); ((260%N, 1%N), 5); ((260%N, 16%N), 9); ((264%N, 1%N), 5);
  ((264%N, 16%N), 0); ((272%N, 32%N), 1); ((288%N, 16%N), 9); ((289%N, 10%N), 9);
  ((320%N, 16%N), 5); ((384%N, 1%N), 9); ((384%N, 16%N), 9); ((512%N, 0%N), 5);
  ((513%N, 2%N), 3); ((513%N, 32%N), 7); ((514%N, 1%N), 8); ((514%N, 32%N), 7);
  ((516%N, 1%N), 5); ((516%N, 32%N), 0); ((517%N, 10%N), 5); ((520%N, 1%N), 5);
  ((520%N, 32%N), 0); ((528%N, 32%N), 1); ((529%N, 10%N), 5); ((544%N, 16%N), 2);
  ((545%N, 10%N), 2); ((576%N, 32%N), 0); ((577%N, 10%N), 5); ((640%N, 1%N), 8);
  ((640%N, 32%N), 8); ((641%N, 10%N), 8); ((768%N, 16%N), 7); ((768%N, 32%N), 7);
  ((769%N, 10%N), 7); ((1024%N, 0%N), 4); ((1025%N, 2%N), 5); ((1026%N, 1%N), 5);
  ((1028%N, 1%N), 5); ((1032%N, 1%N), 5); ((1040%N, 32%N), 0); ((1056%N, 16%N), 2);
  ((1057%N, 10%N), 9); ((1152%N, 1%N), 5); ((1280%N, 16%N), 5); ((1536%N, 32%N), 0);
  ((1537%N, 10%N), 5); ((2048%N, 0%N), 0); ((2049%N, 2%N), 5); ((2050%N, 1%N), 5);
  ((2052%N, 1%N), 5); ((2056%N, 1%N), 5); ((2064%N, 32%N), 0); ((2080%N, 16%N), 0);
  ((2081%N, 10%N), 9); ((2176%N, 1%N), 5); ((2304%N, 16%N), 0); ((2560%N, 32%N), 0);
  ((2561%N, 10%N), 5)
].

Theorem G3R3C2D_verified : verify_gadgetb gadget_3R3C2D = true.
Proof. vm_compute. reflexivity. Qed.

Definition gadget_4R4C : GadgetSpec := mk_gadget_spec
  12
  [ [0; 1; 2]; [3; 4; 5]; [6; 7; 8]; [9; 10; 11]; [0; 6; 9]; [3; 7; 10]; [1; 4; 8]; [2; 5; 11] ]
  [
  (13%N, 530%N); (14%N, 529%N); (41%N, 530%N); (44%N, 2576%N); (112%N, 137%N);
  (134%N, 73%N); (137%N, 1538%N); (137%N, 1552%N); (140%N, 1552%N); (262%N, 25%N);
  (276%N, 11%N); (290%N, 25%N); (324%N, 137%N); (352%N, 137%N); (352%N, 140%N);
  (388%N, 73%N); (560%N, 1033%N); (592%N, 11%N); (608%N, 13%N); (770%N, 25%N);
  (784%N, 11%N); (832%N, 137%N); (896%N, 73%N); (1030%N, 521%N); (1154%N, 25%N);
  (1156%N, 41%N); (1282%N, 25%N); (1296%N, 11%N); (1344%N, 137%N); (1408%N, 73%N);
  (2054%N, 41%N); (2060%N, 560%N); (2066%N, 388%N); (2068%N, 41%N); (2072%N, 164%N);
  (2082%N, 13%N); (2096%N, 140%N); (2116%N, 41%N); (2144%N, 13%N); (2180%N, 41%N);
  (2184%N, 1552%N); (2208%N, 13%N); (2306%N, 25%N); (2308%N, 41%N); (2320%N, 134%N);
  (2336%N, 134%N); (2368%N, 137%N); (2432%N, 73%N); (2562%N, 1033%N); (2568%N, 1156%N);
  (2576%N, 1033%N); (2576%N, 1034%N); (2576%N, 1156%N); (2624%N, 1033%N); (2688%N, 1033%N);
  (2816%N, 1033%N); (2816%N, 1154%N); (2816%N, 1156%N); (3074%N, 521%N); (3136%N, 521%N);
  (3200%N, 521%N); (3328%N, 521%N); (5%N, 34%N); (6%N, 9%N); (9%N, 514%N);
  (9%N, 528%N); (10%N, 17%N); (12%N, 33%N); (12%N, 528%N); (17%N, 10%N);
  (18%N, 257%N); (20%N, 9%N); (24%N, 34%N); (33%N, 12%N); (33%N, 514%N);
  (34%N, 9%N); (36%N, 2049%N); (40%N, 20%N); (48%N, 10%N); (48%N, 12%N);
  (65%N, 514%N); (68%N, 9%N); (72%N, 129%N); (72%N, 144%N); (80%N, 10%N);
  (80%N, 129%N); (96%N, 9%N); (96%N, 12%N); (129%N, 66%N); (129%N, 72%N);
  (130%N, 17%N); (130%N, 72%N); (132%N, 9%N); (136%N, 1040%N); (144%N, 10%N);
  (160%N, 12%N); (192%N, 257%N); (192%N, 264%N); (258%N, 17%N); (260%N, 9%N);
  (260%N, 34%N); (264%N, 130%N); (272%N, 10%N); (288%N, 12%N); (288%N, 130%N);
  (320%N, 129%N); (320%N, 130%N); (384%N, 66%N); (384%N, 72%N); (513%N, 66%N);
  (514%N, 9%N); (520%N, 1025%N); (520%N, 1040%N); (528%N, 9%N); (528%N, 10%N);
  (544%N, 12%N); (544%N, 1025%N); (576%N, 9%N); (640%N, 9%N); (768%N, 9%N);
  (768%N, 66%N); (1025%N, 514%N); (1025%N, 520%N); (1026%N, 9%N); (1028%N, 33%N);
  (1028%N, 520%N); (1032%N, 144%N); (1040%N, 10%N); (1056%N, 12%N); (1088%N, 9%N);
  (1152%N, 9%N); (1280%N, 9%N); (1280%N, 130%N); (1536%N, 2049%N); (1536%N, 2056%N);
  (2049%N, 514%N); (2050%N, 9%N); (2050%N, 20%N); (2052%N, 33%N); (2056%N, 132%N);
  (2056%N, 528%N); (2064%N, 10%N); (2064%N, 132%N); (2080%N, 12%N); (2112%N, 9%N);
  (2112%N, 516%N); (2176%N, 9%N); (2176%N, 1028%N); (2304%N, 130%N); (2304%N, 132%N);
  (2560%N, 1025%N); (2560%N, 1028%N); (3072%N, 516%N); (3072%N, 520%N); (1%N, 2%N);
  (2%N, 1%N); (4%N, 1%N); (8%N, 16%N); (16%N, 2%N); (32%N, 4%N);
  (64%N, 1%N); (128%N, 8%N); (256%N, 2%N); (512%N, 1%N); (1024%N, 8%N);
  (2048%N, 4%N); (0%N, 0%N)
]
  [
  ((1%N, 0%N), 1); ((2%N, 0%N), 0); ((4%N, 0%N), 0); ((5%N, 2%N), 5);
  ((6%N, 1%N), 3); ((8%N, 0%N), 4); ((9%N, 2%N), 9); ((9%N, 16%N), 9);
  ((10%N, 1%N), 4); ((10%N, 16%N), 0); ((11%N, 528%N), 2); ((12%N, 1%N), 5);
  ((12%N, 16%N), 9); ((13%N, 34%N), 6); ((13%N, 514%N), 5); ((13%N, 528%N), 1);
  ((14%N, 17%N), 7); ((14%N, 33%N), 7); ((14%N, 528%N), 0); ((16%N, 0%N), 1);
  ((17%N, 2%N), 3); ((18%N, 1%N), 8); ((20%N, 1%N), 3); ((20%N, 2%N), 5);
  ((21%N, 10%N), 6); ((21%N, 34%N), 6); ((22%N, 9%N), 8); ((22%N, 257%N), 3);
  ((24%N, 2%N), 5); ((25%N, 34%N), 9); ((25%N, 514%N), 5); ((26%N, 257%N), 5);
  ((28%N, 33%N), 7); ((28%N, 34%N), 6); ((32%N, 0%N), 2); ((33%N, 2%N), 9);
  ((33%N, 4%N), 3); ((34%N, 1%N), 3); ((34%N, 4%N), 4); ((35%N, 12%N), 6);
  ((36%N, 1%N), 11); ((37%N, 514%N), 11); ((38%N, 9%N), 11); ((38%N, 2049%N), 3);
  ((40%N, 4%N), 4); ((40%N, 16%N), 2); ((41%N, 20%N), 9); ((41%N, 514%N), 4);
  ((41%N, 528%N), 2); ((42%N, 17%N), 7); ((42%N, 20%N), 6); ((44%N, 528%N), 11);
  ((44%N, 2049%N), 4); ((45%N, 530%N), 11); ((45%N, 2576%N), 1); ((46%N, 529%N), 11);
  ((46%N, 2576%N), 0); ((48%N, 2%N), 3); ((48%N, 4%N), 3); ((49%N, 10%N), 6);
  ((49%N, 12%N), 6); ((49%N, 514%N), 3); ((50%N, 9%N), 8); ((50%N, 12%N), 8);
  ((50%N, 257%N), 3); ((52%N, 9%N), 11); ((52%N, 10%N), 11); ((52%N, 2049%N), 3);
  ((64%N, 0%N), 0); ((65%N, 2%N), 9); ((66%N, 1%N), 8); ((68%N, 1%N), 3);
  ((69%N, 34%N), 9); ((69%N, 514%N), 5); ((70%N, 9%N), 8); ((72%N, 1%N), 7);
  ((72%N, 16%N), 7); ((73%N, 144%N), 9); ((73%N, 514%N), 7); ((73%N, 528%N), 7);
  ((74%N, 17%N), 7); ((74%N, 129%N), 4); ((74%N, 144%N), 0); ((76%N, 33%N), 7);
  ((76%N, 129%N), 5); ((76%N, 144%N), 9); ((76%N, 528%N), 7); ((77%N, 530%N), 7);
  ((78%N, 529%N), 7); ((80%N, 1%N), 7); ((80%N, 2%N), 3); ((81%N, 10%N), 9);
  ((81%N, 514%N), 3); ((82%N, 129%N), 8); ((82%N, 257%N), 3); ((84%N, 9%N), 8);
  ((84%N, 10%N), 9); ((84%N, 129%N), 5); ((88%N, 34%N), 7); ((88%N, 129%N), 5);
  ((96%N, 1%N), 3); ((96%N, 4%N), 3); ((97%N, 12%N), 9); ((97%N, 514%N), 3);
  ((98%N, 9%N), 8); ((98%N, 12%N), 8); ((100%N, 9%N), 11); ((100%N, 2049%N), 3);
  ((104%N, 20%N), 7); ((104%N, 129%N), 4); ((104%N, 144%N), 2); ((105%N, 530%N), 7);
  ((108%N, 2576%N), 7); ((112%N, 9%N), 8); ((112%N, 10%N), 9); ((112%N, 12%N), 8);
  ((112%N, 129%N), 3); ((114%N, 137%N), 8); ((116%N, 137%N), 11); ((128%N, 0%N), 3);
  ((129%N, 2%N), 6); ((129%N, 8%N), 6); ((130%N, 1%N), 4); ((130%N, 8%N), 6);
  ((131%N, 72%N), 2); ((132%N, 1%N), 3); ((132%N, 8%N), 0); ((133%N, 34%N), 6);
  ((133%N, 66%N), 5); ((133%N, 72%N), 1); ((134%N, 9%N), 8); ((134%N, 17%N), 10);
  ((134%N, 72%N), 0); ((136%N, 16%N), 10); ((137%N, 66%N), 10); ((137%N, 514%N), 10);
  ((137%N, 528%N), 10); ((137%N, 1040%N), 6); ((138%N, 17%N), 10); ((138%N, 1040%N), 0);
  ((139%N, 1552%N), 2); ((140%N, 33%N), 10); ((140%N, 528%N), 10); ((140%N, 1040%N), 0);
  ((141%N, 530%N), 10); ((141%N, 1538%N), 5); ((141%N, 1552%N), 1); ((142%N, 529%N), 10);
  ((142%N, 1552%N), 0); ((144%N, 2%N), 3); ((144%N, 8%N), 8); ((145%N, 10%N), 6);
  ((145%N, 66%N), 3); ((145%N, 72%N), 1); ((146%N, 72%N), 8); ((146%N, 257%N), 3);
  ((148%N, 9%N), 8); ((148%N, 10%N), 6); ((150%N, 73%N), 8); ((152%N, 34%N), 10);
  ((153%N, 1538%N), 5); ((160%N, 4%N), 3); ((160%N, 8%N), 2); ((161%N, 12%N), 6);
  ((161%N, 66%N), 3); ((161%N, 72%N), 1); ((161%N, 514%N), 3); ((162%N, 9%N), 8);
  ((162%N, 12%N), 6); ((162%N, 17%N), 10); ((162%N, 72%N), 2); ((164%N, 9%N), 11);
  ((164%N, 2049%N), 3); ((166%N, 73%N), 11); ((168%N, 20%N), 10); ((168%N, 1040%N), 2);
  ((169%N, 530%N), 10); ((169%N, 1538%N), 4); ((169%N, 1552%N), 1); ((172%N, 1552%N), 11);
  ((172%N, 2576%N), 10); ((176%N, 10%N), 6); ((176%N, 12%N), 6); ((192%N, 1%N), 8);
  ((192%N, 8%N), 8); ((193%N, 264%N), 9); ((193%N, 514%N), 8); ((194%N, 17%N), 8);
  ((194%N, 257%N), 4); ((194%N, 264%N), 0); ((196%N, 9%N), 8); ((196%N, 257%N), 3);
  ((196%N, 264%N), 0); ((200%N, 257%N), 10); ((200%N, 1040%N), 8); ((201%N, 1538%N), 8);
  ((201%N, 1552%N), 8); ((204%N, 1552%N), 8); ((208%N, 10%N), 8); ((208%N, 257%N), 3);
  ((208%N, 264%N), 0); ((224%N, 9%N), 8); ((224%N, 12%N), 8); ((224%N, 257%N), 3);
  ((224%N, 264%N), 0); ((256%N, 0%N), 1); ((257%N, 2%N), 6); ((258%N, 1%N), 4);
  ((260%N, 1%N), 3); ((260%N, 2%N), 5); ((261%N, 34%N), 6); ((262%N, 9%N), 4);
  ((262%N, 17%N), 7); ((264%N, 2%N), 7); ((264%N, 16%N), 7); ((265%N, 130%N), 9);
  ((265%N, 514%N), 7); ((265%N, 528%N), 7); ((266%N, 17%N), 7); ((268%N, 33%N), 7);
  ((268%N, 34%N), 6); ((268%N, 130%N), 5); ((268%N, 528%N), 7); ((269%N, 530%N), 7);
  ((270%N, 529%N), 7); ((272%N, 2%N), 3); ((273%N, 10%N), 6); ((276%N, 9%N), 1);
  ((276%N, 10%N), 6); ((276%N, 34%N), 6); ((280%N, 34%N), 6); ((280%N, 130%N), 5);
  ((288%N, 2%N), 7); ((288%N, 4%N), 3); ((289%N, 12%N), 6); ((289%N, 130%N), 9);
  ((289%N, 514%N), 3); ((290%N, 9%N), 4); ((290%N, 12%N), 4); ((290%N, 17%N), 7);
  ((292%N, 9%N), 11); ((292%N, 130%N), 11); ((292%N, 2049%N), 3); ((294%N, 25%N), 11);
  ((296%N, 20%N), 6); ((296%N, 130%N), 4); ((297%N, 530%N), 7); ((300%N, 2576%N), 7);
  ((304%N, 10%N), 6); ((304%N, 12%N), 1); ((304%N, 130%N), 3); ((308%N, 11%N), 11);
  ((320%N, 1%N), 7); ((320%N, 2%N), 7); ((321%N, 130%N), 9); ((321%N, 514%N), 7);
  ((322%N, 17%N), 7); ((322%N, 129%N), 4); ((324%N, 9%N), 7); ((324%N, 34%N), 7);
  ((324%N, 129%N), 4); ((324%N, 130%N), 5); ((326%N, 25%N), 7); ((326%N, 137%N), 4);
  ((328%N, 129%N), 4); ((328%N, 130%N), 5); ((328%N, 144%N), 0); ((336%N, 10%N), 7);
  ((336%N, 129%N), 1); ((336%N, 130%N), 0); ((340%N, 11%N), 7); ((340%N, 137%N), 1);
  ((352%N, 9%N), 7); ((352%N, 12%N), 7); ((352%N, 129%N), 4); ((352%N, 130%N), 9);
  ((353%N, 140%N), 9); ((354%N, 25%N), 7); ((354%N, 137%N), 4); ((354%N, 140%N), 4);
  ((356%N, 137%N), 11); ((368%N, 137%N), 1); ((368%N, 140%N), 1); ((384%N, 2%N), 6);
  ((384%N, 8%N), 6); ((385%N, 66%N), 3); ((385%N, 72%N), 1); ((386%N, 17%N), 6);
  ((386%N, 72%N), 4); ((388%N, 9%N), 6); ((388%N, 34%N), 6); ((388%N, 66%N), 3);
  ((388%N, 72%N), 1); ((390%N, 25%N), 6); ((390%N, 73%N), 4); ((392%N, 66%N), 10);
  ((392%N, 1040%N), 6); ((393%N, 1538%N), 6); ((393%N, 1552%N), 6); ((396%N, 1552%N), 6);
  ((400%N, 10%N), 6); ((400%N, 66%N), 3); ((400%N, 72%N), 1); ((404%N, 11%N), 6);
  ((404%N, 73%N), 1); ((416%N, 12%N), 6); ((416%N, 66%N), 3); ((416%N, 72%N), 2);
  ((418%N, 25%N), 6); ((420%N, 73%N), 11); ((512%N, 0%N), 0); ((513%N, 2%N), 6);
  ((514%N, 1%N), 3); ((516%N, 1%N), 11); ((517%N, 34%N), 6); ((517%N, 66%N), 5);
  ((518%N, 9%N), 11); ((520%N, 1%N), 10); ((520%N, 16%N), 10); ((521%N, 66%N), 10);
  ((521%N, 1040%N), 6); ((522%N, 17%N), 7); ((522%N, 1025%N), 4); ((522%N, 1040%N), 0);
  ((524%N, 33%N), 7); ((524%N, 1025%N), 4); ((524%N, 1040%N), 0); ((528%N, 1%N), 3);
  ((528%N, 2%N), 3); ((529%N, 10%N), 6); ((529%N, 66%N), 3); ((530%N, 9%N), 8);
  ((530%N, 257%N), 3); ((532%N, 9%N), 11); ((532%N, 10%N), 11); ((536%N, 34%N), 7);
  ((536%N, 1025%N), 5); ((544%N, 1%N), 10); ((544%N, 4%N), 3); ((545%N, 12%N), 6);
  ((545%N, 66%N), 10); ((546%N, 9%N), 11); ((546%N, 12%N), 6); ((546%N, 1025%N), 4);
  ((548%N, 1025%N), 11); ((548%N, 2049%N), 3); ((552%N, 20%N), 7); ((552%N, 1025%N), 4);
  ((552%N, 1040%N), 0); ((560%N, 9%N), 11); ((560%N, 10%N), 11); ((560%N, 12%N), 6);
  ((560%N, 1025%N), 3); ((562%N, 1033%N), 8); ((564%N, 1033%N), 11); ((576%N, 1%N), 3);
  ((578%N, 9%N), 8); ((580%N, 9%N), 11); ((584%N, 129%N), 4); ((584%N, 144%N), 0);
  ((584%N, 1025%N), 4); ((584%N, 1040%N), 0); ((592%N, 9%N), 8); ((592%N, 10%N), 0);
  ((592%N, 129%N), 5); ((596%N, 11%N), 11); ((608%N, 9%N), 11); ((608%N, 12%N), 0);
  ((608%N, 1025%N), 4); ((610%N, 13%N), 8); ((624%N, 11%N), 11); ((624%N, 13%N), 8);
  ((624%N, 137%N), 11); ((624%N, 1033%N), 8); ((640%N, 1%N), 3); ((640%N, 8%N), 0);
  ((641%N, 66%N), 3); ((641%N, 72%N), 1); ((642%N, 9%N), 8); ((642%N, 17%N), 10);
  ((642%N, 72%N), 2); ((644%N, 9%N), 11); ((646%N, 73%N), 11); ((648%N, 1025%N), 4);
  ((648%N, 1040%N), 0); ((656%N, 9%N), 8); ((656%N, 10%N), 6); ((672%N, 9%N), 11);
  ((672%N, 12%N), 6); ((672%N, 1025%N), 4); ((688%N, 1033%N), 8); ((704%N, 9%N), 8);
  ((704%N, 257%N), 3); ((704%N, 264%N), 0); ((720%N, 11%N), 8); ((736%N, 13%N), 8);
  ((768%N, 1%N), 3); ((768%N, 2%N), 6); ((769%N, 66%N), 3); ((770%N, 9%N), 4);
  ((770%N, 17%N), 7); ((772%N, 9%N), 11); ((772%N, 34%N), 6); ((772%N, 66%N), 5);
  ((774%N, 25%N), 11); ((776%N, 66%N), 10); ((776%N, 130%N), 5); ((776%N, 1025%N), 4);
  ((776%N, 1040%N), 0); ((784%N, 9%N), 1); ((784%N, 10%N), 6); ((784%N, 66%N), 3);
  ((788%N, 11%N), 11); ((800%N, 9%N), 11); ((800%N, 12%N), 6); ((800%N, 66%N), 10);
  ((800%N, 130%N), 11); ((800%N, 1025%N), 4); ((802%N, 25%N), 11); ((816%N, 11%N), 11);
  ((816%N, 1033%N), 1); ((832%N, 9%N), 7); ((832%N, 129%N), 4); ((832%N, 130%N), 0);
  ((834%N, 25%N), 7); ((834%N, 137%N), 4); ((836%N, 137%N), 11); ((848%N, 11%N), 7);
  ((848%N, 137%N), 1); ((864%N, 13%N), 7); ((864%N, 137%N), 2); ((864%N, 140%N), 0);
  ((896%N, 9%N), 6); ((896%N, 66%N), 3); ((896%N, 72%N), 1); ((898%N, 25%N), 6);
  ((898%N, 73%N), 4); ((900%N, 73%N), 11); ((912%N, 11%N), 6); ((912%N, 73%N), 1);
  ((928%N, 73%N), 11); ((1024%N, 0%N), 3); ((1025%N, 2%N), 9); ((1025%N, 8%N), 9);
  ((1026%N, 1%N), 3); ((1026%N, 8%N), 0); ((1027%N, 520%N), 2); ((1028%N, 1%N), 5);
  ((1028%N, 8%N), 9); ((1029%N, 34%N), 6); ((1029%N, 514%N), 3); ((1029%N, 520%N), 1);
  ((1030%N, 9%N), 11); ((1030%N, 33%N), 7); ((1030%N, 520%N), 0); ((1032%N, 16%N), 7);
  ((1033%N, 144%N), 9); ((1033%N, 514%N), 7); ((1033%N, 528%N), 7); ((1034%N, 17%N), 7);
  ((1034%N, 144%N), 0); ((1036%N, 33%N), 7); ((1036%N, 144%N), 9); ((1036%N, 528%N), 7);
  ((1037%N, 530%N), 7); ((1038%N, 529%N), 7); ((1040%N, 2%N), 3); ((1040%N, 8%N), 1);
  ((1041%N, 10%N), 6); ((1041%N, 514%N), 3); ((1041%N, 520%N), 1); ((1042%N, 9%N), 8);
  ((1042%N, 257%N), 3); ((1044%N, 9%N), 11); ((1044%N, 10%N), 9); ((1044%N, 33%N), 7);
  ((1044%N, 520%N), 1); ((1046%N, 521%N), 8); ((1048%N, 34%N), 7); ((1056%N, 4%N), 3);
  ((1056%N, 8%N), 11); ((1057%N, 12%N), 6); ((1057%N, 514%N), 3); ((1057%N, 520%N), 1);
  ((1058%N, 9%N), 11); ((1058%N, 12%N), 6); ((1060%N, 520%N), 11); ((1060%N, 2049%N), 3);
  ((1062%N, 521%N), 11); ((1064%N, 20%N), 7); ((1064%N, 144%N), 2); ((1065%N, 530%N), 7);
  ((1068%N, 2576%N), 7); ((1072%N, 10%N), 9); ((1072%N, 12%N), 6); ((1088%N, 1%N), 3);
  ((1088%N, 8%N), 0); ((1089%N, 514%N), 3); ((1089%N, 520%N), 1); ((1090%N, 9%N), 8);
  ((1092%N, 9%N), 11); ((1092%N, 33%N), 7); ((1092%N, 520%N), 1); ((1094%N, 521%N), 8);
  ((1096%N, 129%N), 4); ((1096%N, 144%N), 0); ((1104%N, 9%N), 8); ((1104%N, 10%N), 9);
  ((1104%N, 129%N), 5); ((1120%N, 9%N), 11); ((1120%N, 12%N), 9); ((1136%N, 137%N), 11);
  ((1152%N, 8%N), 0); ((1153%N, 66%N), 3); ((1153%N, 72%N), 1); ((1153%N, 514%N), 3);
  ((1153%N, 520%N), 1); ((1154%N, 9%N), 8); ((1154%N, 17%N), 3); ((1154%N, 72%N), 2);
  ((1156%N, 9%N), 11); ((1156%N, 33%N), 3); ((1156%N, 520%N), 1); ((1158%N, 25%N), 11);
  ((1158%N, 41%N), 8); ((1158%N, 73%N), 11); ((1158%N, 521%N), 8); ((1168%N, 9%N), 8);
  ((1168%N, 10%N), 6); ((1172%N, 41%N), 8); ((1184%N, 9%N), 11); ((1184%N, 12%N), 6);
  ((1186%N, 25%N), 11); ((1216%N, 9%N), 8); ((1216%N, 257%N), 3); ((1216%N, 264%N), 0);
  ((1218%N, 25%N), 8); ((1220%N, 41%N), 8); ((1280%N, 2%N), 7); ((1280%N, 8%N), 0);
  ((1281%N, 130%N), 9); ((1281%N, 514%N), 3); ((1281%N, 520%N), 1); ((1282%N, 9%N), 4);
  ((1282%N, 17%N), 7); ((1284%N, 9%N), 11); ((1284%N, 33%N), 7); ((1284%N, 34%N), 6);
  ((1284%N, 130%N), 5); ((1284%N, 520%N), 1); ((1286%N, 25%N), 11); ((1286%N, 521%N), 4);
  ((1288%N, 130%N), 5); ((1288%N, 144%N), 0); ((1296%N, 9%N), 1); ((1296%N, 10%N), 6);
  ((1296%N, 130%N), 5); ((1300%N, 11%N), 11); ((1312%N, 9%N), 11); ((1312%N, 12%N), 6);
  ((1312%N, 130%N), 9); ((1314%N, 25%N), 11); ((1328%N, 11%N), 11); ((1344%N, 9%N), 7);
  ((1344%N, 129%N), 4); ((1344%N, 130%N), 9); ((1346%N, 25%N), 7); ((1346%N, 137%N), 4);
  ((1348%N, 137%N), 11); ((1360%N, 11%N), 7); ((1360%N, 137%N), 1); ((1376%N, 137%N), 11);
  ((1376%N, 140%N), 9); ((1408%N, 9%N), 6); ((1408%N, 66%N), 3); ((1408%N, 72%N), 1);
  ((1410%N, 25%N), 6); ((1410%N, 73%N), 4); ((1412%N, 41%N), 6); ((1412%N, 73%N), 11);
  ((1424%N, 11%N), 6); ((1424%N, 73%N), 1); ((1440%N, 73%N), 11); ((1536%N, 1%N), 11);
  ((1536%N, 8%N), 11); ((1537%N, 66%N), 11); ((1537%N, 2056%N), 6); ((1538%N, 9%N), 11);
  ((1538%N, 2049%N), 3); ((1538%N, 2056%N), 0); ((1540%N, 33%N), 11); ((1540%N, 2049%N), 5);
  ((1540%N, 2056%N), 0); ((1544%N, 144%N), 11); ((1544%N, 2049%N), 7); ((1552%N, 9%N), 11);
  ((1552%N, 10%N), 11); ((1552%N, 2049%N), 3); ((1552%N, 2056%N), 0); ((1568%N, 12%N), 11);
  ((1568%N, 2049%N), 3); ((1568%N, 2056%N), 0); ((1600%N, 9%N), 11); ((1600%N, 2049%N), 3);
  ((1600%N, 2056%N), 0); ((1616%N, 11%N), 11); ((1632%N, 13%N), 11); ((1664%N, 9%N), 11);
  ((1664%N, 2049%N), 3); ((1664%N, 2056%N), 0); ((1666%N, 25%N), 11); ((1668%N, 41%N), 11);
  ((1792%N, 9%N), 11); ((1792%N, 66%N), 11); ((1792%N, 130%N), 11); ((1792%N, 2049%N), 3);
  ((1792%N, 2056%N), 0); ((1794%N, 25%N), 11); ((1808%N, 11%N), 11); ((1856%N, 137%N), 11);
  ((1920%N, 73%N), 11); ((2048%N, 0%N), 2); ((2049%N, 2%N), 9); ((2049%N, 4%N), 9);
  ((2050%N, 1%N), 3); ((2050%N, 4%N), 4); ((2051%N, 20%N), 6); ((2052%N, 1%N), 5);
  ((2053%N, 34%N), 6); ((2053%N, 514%N), 5); ((2054%N, 9%N), 5); ((2054%N, 33%N), 7);
  ((2056%N, 4%N), 7); ((2056%N, 16%N), 9); ((2057%N, 132%N), 9); ((2057%N, 514%N), 5);
  ((2057%N, 528%N), 2); ((2058%N, 17%N), 7); ((2058%N, 20%N), 9); ((2058%N, 132%N), 4);
  ((2058%N, 528%N), 2); ((2060%N, 33%N), 7); ((2060%N, 528%N), 5); ((2061%N, 530%N), 5);
  ((2061%N, 560%N), 1); ((2062%N, 529%N), 5); ((2062%N, 560%N), 0); ((2064%N, 2%N), 3);
  ((2064%N, 4%N), 7); ((2065%N, 10%N), 6); ((2065%N, 132%N), 9); ((2065%N, 514%N), 3);
  ((2066%N, 9%N), 8); ((2066%N, 132%N), 8); ((2066%N, 257%N), 3); ((2067%N, 388%N), 9);
  ((2068%N, 9%N), 5); ((2068%N, 10%N), 5); ((2068%N, 33%N), 7); ((2070%N, 41%N), 8);
  ((2072%N, 34%N), 7); ((2072%N, 132%N), 5); ((2073%N, 164%N), 9); ((2074%N, 164%N), 8);
  ((2074%N, 388%N), 5); ((2080%N, 4%N), 3); ((2081%N, 12%N), 6); ((2081%N, 514%N), 2);
  ((2082%N, 9%N), 2); ((2082%N, 12%N), 6); ((2082%N, 20%N), 6); ((2088%N, 20%N), 7);
  ((2088%N, 132%N), 4); ((2088%N, 528%N), 2); ((2089%N, 530%N), 2); ((2096%N, 10%N), 2);
  ((2096%N, 12%N), 1); ((2096%N, 132%N), 3); ((2097%N, 140%N), 9); ((2098%N, 13%N), 8);
  ((2098%N, 140%N), 8); ((2098%N, 388%N), 3); ((2112%N, 1%N), 3); ((2112%N, 4%N), 9);
  ((2113%N, 514%N), 3); ((2113%N, 516%N), 3); ((2114%N, 9%N), 8); ((2114%N, 20%N), 9);
  ((2114%N, 516%N), 4); ((2116%N, 9%N), 5); ((2116%N, 33%N), 7); ((2118%N, 41%N), 8);
  ((2120%N, 129%N), 4); ((2120%N, 132%N), 9); ((2120%N, 144%N), 0); ((2120%N, 516%N), 7);
  ((2120%N, 528%N), 7); ((2124%N, 560%N), 7); ((2128%N, 9%N), 8); ((2128%N, 10%N), 9);
  ((2128%N, 129%N), 5); ((2128%N, 132%N), 9); ((2128%N, 516%N), 7); ((2130%N, 388%N), 9);
  ((2132%N, 41%N), 8); ((2136%N, 164%N), 9); ((2144%N, 9%N), 2); ((2144%N, 12%N), 9);
  ((2144%N, 516%N), 3); ((2146%N, 13%N), 8); ((2160%N, 13%N), 7); ((2160%N, 137%N), 2);
  ((2160%N, 140%N), 0); ((2176%N, 4%N), 10); ((2176%N, 8%N), 0); ((2177%N, 66%N), 3);
  ((2177%N, 72%N), 1); ((2177%N, 514%N), 3); ((2177%N, 1028%N), 6); ((2178%N, 9%N), 8);
  ((2178%N, 17%N), 10); ((2178%N, 20%N), 9); ((2178%N, 72%N), 2); ((2178%N, 1028%N), 4);
  ((2180%N, 9%N), 5); ((2180%N, 33%N), 10); ((2182%N, 41%N), 8); ((2182%N, 73%N), 5);
  ((2184%N, 528%N), 10); ((2184%N, 1028%N), 4); ((2184%N, 1040%N), 0); ((2185%N, 1538%N), 5);
  ((2185%N, 1552%N), 2); ((2186%N, 1552%N), 2); ((2188%N, 560%N), 10); ((2188%N, 1552%N), 5);
  ((2192%N, 9%N), 8); ((2192%N, 10%N), 6); ((2192%N, 1028%N), 6); ((2196%N, 41%N), 8);
  ((2208%N, 9%N), 2); ((2208%N, 12%N), 6); ((2208%N, 1028%N), 4); ((2210%N, 13%N), 8);
  ((2216%N, 1552%N), 2); ((2224%N, 13%N), 8); ((2240%N, 9%N), 8); ((2240%N, 257%N), 3);
  ((2240%N, 264%N), 0); ((2240%N, 516%N), 8); ((2240%N, 1028%N), 8); ((2244%N, 41%N), 8);
  ((2248%N, 1552%N), 8); ((2272%N, 13%N), 8); ((2304%N, 2%N), 7); ((2304%N, 4%N), 7);
  ((2305%N, 130%N), 9); ((2305%N, 132%N), 9); ((2305%N, 514%N), 3); ((2306%N, 9%N), 4);
  ((2306%N, 17%N), 7); ((2306%N, 20%N), 6); ((2306%N, 132%N), 4); ((2308%N, 9%N), 5);
  ((2308%N, 33%N), 7); ((2308%N, 34%N), 6); ((2308%N, 130%N), 5); ((2310%N, 25%N), 5);
  ((2310%N, 41%N), 4); ((2312%N, 130%N), 5); ((2312%N, 132%N), 4); ((2312%N, 528%N), 7);
  ((2316%N, 560%N), 7); ((2320%N, 10%N), 6); ((2320%N, 130%N), 5); ((2320%N, 132%N), 1);
  ((2321%N, 134%N), 9); ((2324%N, 11%N), 5); ((2324%N, 41%N), 1); ((2328%N, 134%N), 5);
  ((2328%N, 164%N), 1); ((2336%N, 12%N), 6); ((2336%N, 130%N), 2); ((2336%N, 132%N), 4);
  ((2337%N, 134%N), 9); ((2338%N, 13%N), 4); ((2338%N, 25%N), 2); ((2344%N, 134%N), 4);
  ((2352%N, 134%N), 3); ((2352%N, 140%N), 1); ((2368%N, 9%N), 7); ((2368%N, 129%N), 4);
  ((2368%N, 130%N), 9); ((2368%N, 132%N), 9); ((2368%N, 516%N), 7); ((2370%N, 25%N), 7);
  ((2370%N, 137%N), 4); ((2372%N, 41%N), 7); ((2372%N, 137%N), 5); ((2384%N, 134%N), 9);
  ((2384%N, 137%N), 1); ((2400%N, 13%N), 7); ((2400%N, 134%N), 9); ((2400%N, 137%N), 2);
  ((2400%N, 140%N), 9); ((2432%N, 9%N), 6); ((2432%N, 66%N), 3); ((2432%N, 72%N), 1);
  ((2432%N, 1028%N), 6); ((2434%N, 25%N), 6); ((2434%N, 73%N), 4); ((2436%N, 41%N), 6);
  ((2436%N, 73%N), 5); ((2440%N, 1552%N), 6); ((2448%N, 73%N), 1); ((2464%N, 13%N), 6);
  ((2464%N, 73%N), 2); ((2560%N, 1%N), 10); ((2560%N, 4%N), 10); ((2561%N, 66%N), 10);
  ((2561%N, 1028%N), 6); ((2562%N, 9%N), 10); ((2562%N, 20%N), 10); ((2562%N, 1025%N), 4);
  ((2562%N, 1028%N), 4); ((2564%N, 33%N), 10); ((2564%N, 1025%N), 5); ((2566%N, 41%N), 10);
  ((2566%N, 1033%N), 5); ((2568%N, 132%N), 10); ((2568%N, 1025%N), 4); ((2568%N, 1028%N), 4);
  ((2568%N, 1040%N), 0); ((2569%N, 1156%N), 6); ((2570%N, 1156%N), 4); ((2576%N, 9%N), 10);
  ((2576%N, 10%N), 10); ((2576%N, 132%N), 10); ((2576%N, 1025%N), 5); ((2576%N, 1028%N), 6);
  ((2577%N, 1034%N), 6); ((2577%N, 1156%N), 6); ((2578%N, 388%N), 10); ((2578%N, 1033%N), 8);
  ((2578%N, 1156%N), 8); ((2580%N, 41%N), 10); ((2580%N, 1033%N), 5); ((2580%N, 1034%N), 5);
  ((2584%N, 164%N), 10); ((2584%N, 1156%N), 5); ((2592%N, 12%N), 10); ((2592%N, 1025%N), 2);
  ((2592%N, 1028%N), 0); ((2594%N, 13%N), 10); ((2594%N, 1033%N), 2); ((2600%N, 1156%N), 4);
  ((2608%N, 140%N), 10); ((2608%N, 1033%N), 2); ((2608%N, 1034%N), 2); ((2608%N, 1156%N), 3);
  ((2624%N, 9%N), 10); ((2624%N, 1025%N), 4); ((2624%N, 1028%N), 0); ((2626%N, 1033%N), 8);
  ((2628%N, 41%N), 10); ((2628%N, 1033%N), 5); ((2632%N, 1156%N), 0); ((2640%N, 11%N), 10);
  ((2640%N, 1033%N), 1); ((2640%N, 1034%N), 0); ((2640%N, 1156%N), 0); ((2656%N, 13%N), 10);
  ((2656%N, 1033%N), 2); ((2688%N, 9%N), 10); ((2688%N, 1025%N), 4); ((2688%N, 1028%N), 6);
  ((2690%N, 1033%N), 8); ((2692%N, 41%N), 10); ((2692%N, 1033%N), 5); ((2704%N, 1033%N), 8);
  ((2704%N, 1034%N), 6); ((2720%N, 13%N), 10); ((2720%N, 1033%N), 2); ((2752%N, 1033%N), 8);
  ((2816%N, 9%N), 10); ((2816%N, 66%N), 10); ((2816%N, 130%N), 10); ((2816%N, 132%N), 10);
  ((2816%N, 1025%N), 4); ((2816%N, 1028%N), 6); ((2817%N, 1154%N), 6); ((2817%N, 1156%N), 6);
  ((2818%N, 25%N), 10); ((2818%N, 1033%N), 4); ((2818%N, 1156%N), 4); ((2820%N, 41%N), 10);
  ((2820%N, 1033%N), 5); ((2820%N, 1154%N), 5); ((2824%N, 1154%N), 5); ((2824%N, 1156%N), 4);
  ((2832%N, 11%N), 10); ((2832%N, 134%N), 10); ((2832%N, 1033%N), 1); ((2832%N, 1034%N), 6);
  ((2832%N, 1154%N), 5); ((2832%N, 1156%N), 1); ((2848%N, 134%N), 10); ((2848%N, 1033%N), 2);
  ((2848%N, 1154%N), 2); ((2848%N, 1156%N), 1); ((2880%N, 137%N), 10); ((2880%N, 1033%N), 7);
  ((2880%N, 1154%N), 0); ((2880%N, 1156%N), 0); ((2944%N, 73%N), 10); ((2944%N, 1033%N), 6);
  ((3072%N, 4%N), 9); ((3072%N, 8%N), 9); ((3073%N, 514%N), 3); ((3073%N, 516%N), 3);
  ((3073%N, 520%N), 1); ((3074%N, 9%N), 9); ((3074%N, 20%N), 9); ((3074%N, 516%N), 3);
  ((3074%N, 520%N), 2); ((3076%N, 33%N), 9); ((3076%N, 520%N), 5); ((3078%N, 41%N), 9);
  ((3078%N, 521%N), 5); ((3080%N, 132%N), 9); ((3080%N, 144%N), 9); ((3080%N, 516%N), 7);
  ((3080%N, 528%N), 7); ((3084%N, 560%N), 7); ((3088%N, 10%N), 9); ((3088%N, 132%N), 9);
  ((3088%N, 516%N), 7); ((3088%N, 520%N), 1); ((3090%N, 388%N), 9); ((3090%N, 521%N), 8);
  ((3092%N, 41%N), 9); ((3096%N, 164%N), 9); ((3104%N, 12%N), 9); ((3104%N, 516%N), 3);
  ((3104%N, 520%N), 2); ((3106%N, 13%N), 9); ((3106%N, 521%N), 2); ((3120%N, 140%N), 9);
  ((3136%N, 9%N), 9); ((3136%N, 516%N), 3); ((3136%N, 520%N), 1); ((3138%N, 521%N), 8);
  ((3140%N, 41%N), 9); ((3140%N, 521%N), 5); ((3152%N, 521%N), 8); ((3168%N, 13%N), 9);
  ((3168%N, 521%N), 2); ((3200%N, 9%N), 9); ((3200%N, 516%N), 3); ((3200%N, 520%N), 1);
  ((3202%N, 25%N), 9); ((3202%N, 521%N), 4); ((3204%N, 41%N), 9); ((3204%N, 521%N), 5);
  ((3216%N, 521%N), 8); ((3232%N, 13%N), 9); ((3232%N, 521%N), 2); ((3264%N, 521%N), 8);
  ((3328%N, 9%N), 9); ((3328%N, 130%N), 9); ((3328%N, 132%N), 9); ((3328%N, 516%N), 7);
  ((3328%N, 520%N), 1); ((3330%N, 25%N), 9); ((3330%N, 521%N), 4); ((3332%N, 41%N), 9);
  ((3332%N, 521%N), 5); ((3344%N, 11%N), 9); ((3344%N, 134%N), 9); ((3344%N, 521%N), 1);
  ((3360%N, 134%N), 9); ((3360%N, 521%N), 2); ((3392%N, 137%N), 9); ((3392%N, 521%N), 7);
  ((3456%N, 73%N), 9); ((3456%N, 521%N), 6)
].

Theorem G4R4C_verified : verify_gadgetb gadget_4R4C = true.
Proof. vm_compute. reflexivity. Qed.

Definition gadget_Slice14 : GadgetSpec := mk_gadget_spec
  14
  [ [0; 1; 2]; [3; 4; 5]; [6; 7; 8; 9]; [10; 11; 12; 13]; [0; 6; 10]; [3; 7; 11]; [1; 4; 8; 12]; [2; 5; 9; 13]; [0; 3; 8; 13]; [2; 4; 7; 10] ]
  [
  (1033%N, 324%N); (2057%N, 388%N); (9%N, 260%N); (24%N, 33%N); (136%N, 2049%N);
  (1%N, 4%N); (4%N, 1%N); (8%N, 1%N); (16%N, 1%N); (128%N, 1%N);
  (512%N, 1%N); (1024%N, 1%N); (4096%N, 1%N); (0%N, 0%N)
]
  [
  ((1%N, 0%N), 2); ((2%N, 0%N), 0); ((3%N, 4%N), 3); ((4%N, 0%N), 0);
  ((6%N, 1%N), 4); ((8%N, 0%N), 0); ((9%N, 4%N), 8); ((10%N, 1%N), 4);
  ((11%N, 260%N), 10); ((12%N, 1%N), 4); ((16%N, 0%N), 0); ((17%N, 4%N), 3);
  ((18%N, 1%N), 7); ((20%N, 1%N), 7); ((24%N, 1%N), 5); ((25%N, 260%N), 5);
  ((26%N, 33%N), 7); ((28%N, 33%N), 7); ((32%N, 0%N), 3); ((33%N, 4%N), 3);
  ((36%N, 1%N), 4); ((40%N, 1%N), 4); ((41%N, 260%N), 4); ((48%N, 1%N), 3);
  ((64%N, 0%N), 0); ((65%N, 4%N), 10); ((68%N, 1%N), 4); ((72%N, 1%N), 4);
  ((73%N, 260%N), 10); ((80%N, 1%N), 7); ((88%N, 33%N), 7); ((128%N, 0%N), 0);
  ((129%N, 4%N), 3); ((130%N, 1%N), 4); ((132%N, 1%N), 4); ((136%N, 1%N), 11);
  ((137%N, 260%N), 11); ((138%N, 2049%N), 4); ((140%N, 2049%N), 4); ((144%N, 1%N), 3);
  ((152%N, 33%N), 11); ((152%N, 2049%N), 5); ((160%N, 1%N), 4); ((168%N, 2049%N), 4);
  ((192%N, 1%N), 4); ((200%N, 2049%N), 4); ((256%N, 0%N), 3); ((257%N, 4%N), 3);
  ((260%N, 1%N), 4); ((264%N, 1%N), 4); ((272%N, 1%N), 7); ((280%N, 33%N), 7);
  ((384%N, 1%N), 4); ((392%N, 2049%N), 4); ((512%N, 0%N), 0); ((513%N, 4%N), 3);
  ((514%N, 1%N), 4); ((516%N, 1%N), 4); ((520%N, 1%N), 4); ((521%N, 260%N), 10);
  ((528%N, 1%N), 7); ((536%N, 33%N), 7); ((544%N, 1%N), 4); ((576%N, 1%N), 4);
  ((640%N, 1%N), 3); ((648%N, 2049%N), 4); ((768%N, 1%N), 4); ((1024%N, 0%N), 0);
  ((1025%N, 4%N), 6); ((1026%N, 1%N), 4); ((1028%N, 1%N), 4); ((1032%N, 1%N), 4);
  ((1033%N, 260%N), 6); ((1035%N, 324%N), 11); ((1040%N, 1%N), 7); ((1048%N, 33%N), 7);
  ((1049%N, 324%N), 5); ((1056%N, 1%N), 4); ((1065%N, 324%N), 4); ((1088%N, 1%N), 4);
  ((1152%N, 1%N), 4); ((1160%N, 2049%N), 4); ((1161%N, 324%N), 11); ((1280%N, 1%N), 4);
  ((1536%N, 1%N), 4); ((1545%N, 324%N), 11); ((2048%N, 0%N), 3); ((2049%N, 4%N), 3);
  ((2052%N, 1%N), 4); ((2056%N, 1%N), 7); ((2057%N, 260%N), 7); ((2059%N, 388%N), 10);
  ((2064%N, 1%N), 7); ((2072%N, 33%N), 7); ((2073%N, 388%N), 5); ((2089%N, 388%N), 4);
  ((2121%N, 388%N), 10); ((2176%N, 1%N), 3); ((2560%N, 1%N), 7); ((2569%N, 388%N), 10);
  ((3072%N, 1%N), 4); ((3081%N, 324%N), 7); ((3081%N, 388%N), 6); ((4096%N, 0%N), 0);
  ((4097%N, 4%N), 3); ((4098%N, 1%N), 4); ((4100%N, 1%N), 4); ((4104%N, 1%N), 4);
  ((4105%N, 260%N), 10); ((4112%N, 1%N), 3); ((4120%N, 33%N), 7); ((4128%N, 1%N), 4);
  ((4160%N, 1%N), 4); ((4224%N, 1%N), 4); ((4232%N, 2049%N), 4); ((4352%N, 1%N), 4);
  ((4608%N, 1%N), 4); ((5120%N, 1%N), 4); ((5129%N, 324%N), 11); ((6144%N, 1%N), 4);
  ((6153%N, 388%N), 10); ((8192%N, 0%N), 0); ((8193%N, 4%N), 3); ((8196%N, 1%N), 4);
  ((8200%N, 1%N), 4); ((8201%N, 260%N), 10); ((8208%N, 1%N), 3); ((8216%N, 33%N), 7);
  ((8320%N, 1%N), 3); ((8328%N, 2049%N), 4); ((8704%N, 1%N), 4); ((9216%N, 1%N), 4);
  ((9225%N, 324%N), 11); ((10249%N, 388%N), 10); ((12288%N, 1%N), 4)
].

Theorem Slice14_verified : verify_gadgetb gadget_Slice14 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem Slice14_sub_phi_28 : sub_phi (gs_frags gadget_Slice14) 0%N 0%N = 28.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions K4_no_es_lt16_partition.
Print Assumptions Slice14_verified.
