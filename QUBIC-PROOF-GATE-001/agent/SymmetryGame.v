(** Full-game symmetry for the locked evaluator, including arbitrary policy
    requests and its non-equivariant lowest-free-cell fallback. *)
From Stdlib Require Import List Arith Bool Lia Permutation.
From QubicTrusted Require Import Rules Goal.
From QubicAgent Require Import Geometry Minimax RulesFacts SafePairing Stealing.
Import ListNotations.

Record BoardIso : Type := {
  forward : cell -> cell;
  backward : cell -> cell;
  forward_bound : forall c, c < 125 -> forward c < 125;
  backward_bound : forall c, c < 125 -> backward c < 125;
  inverse_forward : forall c, c < 125 -> backward (forward c) = c;
  inverse_backward : forall c, c < 125 -> forward (backward c) = c;
  forward_lines : forall l, In l all_lines ->
    exists image, In image all_lines /\ Permutation (map forward l) image;
  backward_lines : forall l, In l all_lines ->
    exists image, In image all_lines /\ Permutation (map backward l) image
}.

Definition reverse_iso (iso : BoardIso) : BoardIso :=
  {| forward := backward iso; backward := forward iso;
     forward_bound := backward_bound iso; backward_bound := forward_bound iso;
     inverse_forward := inverse_backward iso; inverse_backward := inverse_forward iso;
     forward_lines := backward_lines iso; backward_lines := forward_lines iso |}.

Definition transport (iso : BoardIso) (st : GameState) : GameState :=
  make_state (map (forward iso) (white_stones st))
    (map (forward iso) (black_stones st)) (map (forward iso) (history st)).

Definition cells_in_range (xs : list cell) : Prop := forall c, In c xs -> c < 125.

Lemma valid_stone_ranges : forall st, valid_state st ->
  cells_in_range (white_stones st) /\ cells_in_range (black_stones st) /\ cells_in_range (history st).
Proof.
  intros st Hvalid.
  assert (Hh : cells_in_range (history st)).
  { unfold cells_in_range. pose proof (history_valid st Hvalid) as H.
    rewrite Forall_forall in H. exact H. }
  repeat split; try exact Hh; intros c Hc; apply Hh;
    apply (valid_history_occupied st c Hvalid), occupied_spec, in_app_iff; auto.
Qed.

Lemma forward_injective : forall iso x y,
  x < 125 -> y < 125 -> forward iso x = forward iso y -> x = y.
Proof.
  intros iso x y Hx Hy H.
  apply (f_equal (backward iso)) in H.
  rewrite !inverse_forward in H by assumption. exact H.
Qed.

Lemma transport_inverse_list : forall iso xs,
  cells_in_range xs -> map (backward iso) (map (forward iso) xs) = xs.
Proof.
  intros iso xs. induction xs as [|c xs IH]; intros Hr; [reflexivity|].
  cbn. rewrite inverse_forward by (apply Hr; left; reflexivity).
  rewrite IH; [reflexivity|]. intros d Hd. apply Hr. right. exact Hd.
Qed.

Lemma transport_inverse : forall iso st,
  valid_state st -> transport (reverse_iso iso) (transport iso st) = st.
Proof.
  intros iso st Hvalid.
  destruct (valid_stone_ranges st Hvalid) as [Hw [Hb Hh]].
  unfold transport, reverse_iso. cbn [forward white_stones black_stones history].
  rewrite !transport_inverse_list by assumption. destruct st. reflexivity.
Qed.

Lemma nodup_map_bounded : forall iso xs,
  cells_in_range xs -> NoDup xs -> NoDup (map (forward iso) xs).
Proof.
  intros iso xs. induction xs as [|c xs IH]; intros Hr Hnd; [constructor|].
  inversion Hnd as [|? ? Hnot Htail]; subst. cbn. constructor.
  - intros Hin. apply in_map_iff in Hin as [d [Heq Hd]].
    assert (Hcd : d = c) by
      (apply forward_injective with (iso := iso); [apply Hr; right; exact Hd|apply Hr; left; reflexivity|exact Heq]).
    subst d. contradiction.
  - apply IH; [intros d Hd; apply Hr; right; exact Hd|exact Htail].
Qed.

Lemma transport_valid : forall iso st, valid_state st -> valid_state (transport iso st).
Proof.
  intros iso st Hvalid.
  destruct (valid_stone_ranges st Hvalid) as [Hw [Hb Hh]].
  constructor; cbn [transport history white_stones black_stones].
  - apply Forall_forall. intros c Hc. apply in_map_iff in Hc as [d [<- Hd]].
    apply forward_bound, Hh. exact Hd.
  - apply nodup_map_bounded; [exact Hh|apply history_nodup; exact Hvalid].
  - rewrite <- map_app. apply Permutation_map. apply history_partition. exact Hvalid.
Qed.

Lemma transport_history_length : forall iso st,
  length (history (transport iso st)) = length (history st).
Proof. intros. apply length_map. Qed.

Lemma forward_winning : forall iso stones,
  has_win stones = true -> has_win (map (forward iso) stones) = true.
Proof.
  intros iso stones Hwin. unfold has_win in *.
  apply existsb_exists in Hwin as [l [Hl Hline]].
  destruct (forward_lines iso l Hl) as [image [Himage Hperm]].
  apply existsb_exists. exists image. split; [exact Himage|].
  unfold has_line in *. apply forallb_forall. intros c Hc.
  assert (Hin : In c (map (forward iso) l)) by
    (eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hc]).
  apply in_map_iff in Hin as [d [<- Hd]]. apply member_spec, in_map.
  apply member_spec. apply forallb_forall with (x := d) in Hline; assumption.
Qed.

Lemma transport_winning : forall iso stones,
  cells_in_range stones -> has_win (map (forward iso) stones) = has_win stones.
Proof.
  intros iso stones Hr.
  destruct (has_win stones) eqn:Hsource,
    (has_win (map (forward iso) stones)) eqn:Himage; try reflexivity.
  - pose proof (forward_winning iso stones Hsource). congruence.
  - pose proof (forward_winning (reverse_iso iso) _ Himage) as Hbad.
    change (has_win (map (backward iso) (map (forward iso) stones)) = true) in Hbad.
    rewrite transport_inverse_list in Hbad by exact Hr. congruence.
Qed.

Lemma image_membership : forall iso xs c,
  cells_in_range xs -> c < 125 ->
  (In (forward iso c) (map (forward iso) xs) <-> In c xs).
Proof.
  intros iso xs c Hr Hc. split; [|apply in_map].
  intros H. apply in_map_iff in H as [d [Heq Hd]].
  assert (Hd_eq : d = c) by
    (apply forward_injective with (iso := iso); [apply Hr; exact Hd|exact Hc|exact Heq]).
  subst d. exact Hd.
Qed.

Lemma occupied_transport : forall iso st c,
  valid_state st -> c < 125 ->
  occupied (transport iso st) (forward iso c) = occupied st c.
Proof.
  intros iso st c Hvalid Hc.
  destruct (valid_stone_ranges st Hvalid) as [Hw [Hb Hh]].
  assert (Hiff : occupied (transport iso st) (forward iso c) = true <-> occupied st c = true).
  { rewrite !occupied_spec, !in_app_iff.
    change ((In (forward iso c) (map (forward iso) (white_stones st)) \/
      In (forward iso c) (map (forward iso) (black_stones st))) <->
      In c (white_stones st) \/ In c (black_stones st)).
    rewrite !image_membership by assumption. reflexivity. }
  destruct (occupied (transport iso st) (forward iso c)), (occupied st c);
    try reflexivity; exfalso; intuition discriminate.
Qed.

Lemma legal_transport : forall iso st c,
  valid_state st -> c < 125 ->
  is_legal_move (transport iso st) (forward iso c) = is_legal_move st c.
Proof.
  intros iso st c Hvalid Hc. unfold is_legal_move.
  rewrite occupied_transport by assumption.
  assert (Hsource : (c <? 125) = true) by (apply Nat.ltb_lt; exact Hc).
  assert (Himage : (forward iso c <? 125) = true) by (apply Nat.ltb_lt, forward_bound; exact Hc).
  rewrite Hsource, Himage. reflexivity.
Qed.

(** We transport the EFFECTIVE legal move, not the raw request: the fallback
    chooses the smallest free cell and does not commute with cube rotations. *)
Lemma move_transport : forall iso turn st request,
  valid_state st -> length (history st) < 125 ->
  transport iso (move_state turn st request) =
  move_state turn (transport iso st) (forward iso (effective_move st request)).
Proof.
  intros iso turn st request Hvalid Hspace.
  pose proof (effective_move_is_legal st request Hvalid Hspace) as Hlegal.
  pose proof (legal_move_fresh st _ Hlegal) as [Hbound _].
  assert (Himage : is_legal_move (transport iso st) (forward iso (effective_move st request)) = true)
    by (rewrite legal_transport by assumption; exact Hlegal).
  assert (Heff : effective_move (transport iso st) (forward iso (effective_move st request)) =
    forward iso (effective_move st request)) by (unfold effective_move at 1; rewrite Himage; reflexivity).
  unfold move_state. rewrite Heff. destruct turn; reflexivity.
Qed.

Lemma result_transport : forall iso turn st,
  valid_state st -> move_result turn (transport iso st) = move_result turn st.
Proof.
  intros iso turn st Hvalid.
  destruct (valid_stone_ranges st Hvalid) as [Hw [Hb Hh]].
  unfold move_result, transport. cbn [white_stones black_stones history].
  rewrite length_map. destruct turn; rewrite transport_winning by assumption; reflexivity.
Qed.

Lemma equal_effective_branch : forall accept continuation turn st a b,
  effective_move st a = effective_move st b ->
  branch accept continuation turn st a = branch accept continuation turn st b.
Proof.
  intros accept continuation turn st a b H.
  unfold branch, move_state. rewrite H. reflexivity.
Qed.

Lemma existsb_equal_value_sets : forall (f g : cell -> bool) xs ys,
  (forall x, In x xs -> exists y, In y ys /\ f x = g y) ->
  (forall y, In y ys -> exists x, In x xs /\ f x = g y) ->
  existsb f xs = existsb g ys.
Proof.
  intros f g xs ys Hforward Hback.
  destruct (existsb f xs) eqn:Hf, (existsb g ys) eqn:Hg; try reflexivity.
  - apply existsb_exists in Hf as [x [Hx Hfx]].
    destruct (Hforward x Hx) as [y [Hy Heq]].
    assert (Hbad : existsb g ys = true) by
      (apply existsb_exists; exists y; split; [exact Hy|congruence]). congruence.
  - apply existsb_exists in Hg as [y [Hy Hgy]].
    destruct (Hback y Hy) as [x [Hx Heq]].
    assert (Hbad : existsb f xs = true) by
      (apply existsb_exists; exists x; split; [exact Hx|congruence]). congruence.
Qed.

Lemma forallb_equal_value_sets : forall (f g : cell -> bool) xs ys,
  (forall x, In x xs -> exists y, In y ys /\ f x = g y) ->
  (forall y, In y ys -> exists x, In x xs /\ f x = g y) ->
  forallb f xs = forallb g ys.
Proof.
  intros f g xs ys Hforward Hback.
  destruct (forallb f xs) eqn:Hf, (forallb g ys) eqn:Hg; try reflexivity.
  - apply forallb_false_exists in Hg as [y [Hy Hgy]].
    destruct (Hback y Hy) as [x [Hx Heq]].
    apply forallb_forall with (x := x) in Hf; [congruence|exact Hx].
  - apply forallb_false_exists in Hf as [x [Hx Hfx]].
    destruct (Hforward x Hx) as [y [Hy Heq]].
    apply forallb_forall with (x := y) in Hg; [congruence|exact Hy].
Qed.

Local Opaque solve.

Lemma branch_transport : forall iso accept owner n turn st request,
  (forall next, valid_state next -> n + length (history next) = 125 ->
    solve accept owner n (negb turn) (transport iso next) = solve accept owner n (negb turn) next) ->
  valid_state st -> S n + length (history st) = 125 ->
  branch accept (solve accept owner n) turn (transport iso st)
    (forward iso (effective_move st request)) =
  branch accept (solve accept owner n) turn st request.
Proof.
  intros iso accept owner n turn st request IH Hvalid Hlen.
  assert (Hnext : valid_state (move_state turn st request)) by
    (apply move_preserves_validity; [exact Hvalid|lia]).
  unfold branch. rewrite <- (move_transport iso turn st request Hvalid ltac:(lia)).
  rewrite result_transport by exact Hnext.
  destruct (move_result turn (move_state turn st request)); [reflexivity|].
  apply IH; [exact Hnext|rewrite move_state_history; lia].
Qed.

(** For any terminal acceptance predicate, every finite full-horizon minimax
    value is invariant under a board automorphism. No legality restriction is
    imposed on policies; effective-move simulation covers their fallbacks. *)
Theorem solve_symmetry : forall iso accept owner n turn st,
  valid_state st -> n + length (history st) = 125 ->
  solve accept owner n turn (transport iso st) = solve accept owner n turn st.
Proof.
  intros iso accept owner n. induction n as [|n IH]; intros turn st Hvalid Hlen.
  - rewrite !solve_empty_horizon. reflexivity.
  - rewrite !solve_successor.
    set (source := branch accept (solve accept owner n) turn st).
    set (image := branch accept (solve accept owner n) turn (transport iso st)).
    assert (Hforward : forall request, In request requests ->
      exists mapped, In mapped requests /\ source request = image mapped).
    { intros request Hin. exists (forward iso (effective_move st request)). split.
      - apply in_seq. pose proof (effective_move_is_legal st request Hvalid ltac:(lia)) as Hlegal.
        destruct (legal_move_fresh st _ Hlegal) as [Hbound _].
        pose proof (forward_bound iso _ Hbound). lia.
      - symmetry. apply branch_transport; [apply IH|exact Hvalid|exact Hlen]. }
    assert (Hback : forall request, In request requests ->
      exists original, In original requests /\ source original = image request).
    { intros request Hin.
      set (e := effective_move (transport iso st) request).
      assert (Himage_valid : valid_state (transport iso st)) by (apply transport_valid; exact Hvalid).
      assert (Himage_space : length (history (transport iso st)) < 125)
        by (rewrite transport_history_length; lia).
      assert (Hlegal : is_legal_move (transport iso st) e = true)
        by (apply effective_move_is_legal; assumption).
      destruct (legal_move_fresh _ _ Hlegal) as [He_bound _].
      pose proof (backward_bound iso e He_bound) as Hg_bound.
      exists (backward iso e). split; [apply in_seq; lia|].
      assert (Hsource_legal : is_legal_move st (backward iso e) = true).
      { rewrite <- (legal_transport iso st (backward iso e) Hvalid Hg_bound).
        rewrite inverse_backward by exact He_bound. exact Hlegal. }
      assert (Hsource_eff : effective_move st (backward iso e) = backward iso e)
        by (unfold effective_move at 1; rewrite Hsource_legal; reflexivity).
      pose proof (branch_transport iso accept owner n turn st (backward iso e)
        (IH (negb turn)) Hvalid Hlen) as Hbranch.
      rewrite Hsource_eff, inverse_backward in Hbranch by exact He_bound.
      assert (Himage_eff : effective_move (transport iso st) e = e)
        by (unfold effective_move at 1; rewrite Hlegal; reflexivity).
      assert (Hsame : image request = image e).
      { apply equal_effective_branch. change (e = effective_move (transport iso st) e).
        symmetry. exact Himage_eff. }
      rewrite Hsame. symmetry. exact Hbranch. }
    destruct (Bool.eqb turn owner);
      [symmetry; apply existsb_equal_value_sets|symmetry; apply forallb_equal_value_sets];
      assumption.
Qed.

(** A small executable checker builds trusted isomorphism records from finite
    coordinate functions. Images may reverse their line orientation. *)
Definition isob (f g : cell -> cell) : bool :=
  forallb (fun c => (f c <? 125) && (g c <? 125) &&
    (g (f c) =? c) && (f (g c) =? c)) all_cells &&
  forallb (fun l => contains_line (map f l) oriented_lines) all_lines &&
  forallb (fun l => contains_line (map g l) oriented_lines) all_lines.

Lemma line_images_from_check : forall f,
  forallb (fun l => contains_line (map f l) oriented_lines) all_lines = true ->
  forall l, In l all_lines -> exists image, In image all_lines /\ Permutation (map f l) image.
Proof.
  intros f H l Hl. apply forallb_forall with (x := l) in H; [|exact Hl].
  apply contains_line_spec, oriented_lines_spec in H. destruct H as [H|H].
  - exists (map f l). split; [exact H|reflexivity].
  - exists (rev (map f l)). split; [exact H|apply Permutation_rev].
Qed.

Definition checked_iso (f g : cell -> cell) (H : isob f g = true) : BoardIso.
Proof.
  refine {| forward := f; backward := g |}.
  - intros c Hc. unfold isob in H. rewrite !andb_true_iff in H.
    destruct H as [[Hcells _] _]. apply forallb_forall with (x := c) in Hcells;
      [|apply in_seq; lia]. rewrite !andb_true_iff in Hcells.
    destruct Hcells as [[[Hrange _] _] _]. apply Nat.ltb_lt. exact Hrange.
  - intros c Hc. unfold isob in H. rewrite !andb_true_iff in H.
    destruct H as [[Hcells _] _]. apply forallb_forall with (x := c) in Hcells;
      [|apply in_seq; lia]. rewrite !andb_true_iff in Hcells.
    destruct Hcells as [[[_ Hrange] _] _]. apply Nat.ltb_lt. exact Hrange.
  - intros c Hc. unfold isob in H. rewrite !andb_true_iff in H.
    destruct H as [[Hcells _] _]. apply forallb_forall with (x := c) in Hcells;
      [|apply in_seq; lia]. rewrite !andb_true_iff in Hcells.
    destruct Hcells as [[_ Hinv] _]. apply Nat.eqb_eq. exact Hinv.
  - intros c Hc. unfold isob in H. rewrite !andb_true_iff in H.
    destruct H as [[Hcells _] _]. apply forallb_forall with (x := c) in Hcells;
      [|apply in_seq; lia]. rewrite !andb_true_iff in Hcells.
    destruct Hcells as [_ Hinv]. apply Nat.eqb_eq. exact Hinv.
  - apply line_images_from_check. unfold isob in H. rewrite !andb_true_iff in H. tauto.
  - apply line_images_from_check. unfold isob in H. rewrite !andb_true_iff in H. tauto.
Defined.

Definition identity_iso : BoardIso.
Proof.
  refine {| forward := fun c => c; backward := fun c => c |}; try (intros; assumption);
    try (intros; reflexivity).
  - intros l Hl. exists l. split; [exact Hl|rewrite map_id; reflexivity].
  - intros l Hl. exists l. split; [exact Hl|rewrite map_id; reflexivity].
Defined.

Definition compose_iso (outer inner : BoardIso) : BoardIso.
Proof.
  refine {| forward := fun c => forward outer (forward inner c);
            backward := fun c => backward inner (backward outer c) |}.
  - intros c Hc. apply forward_bound, forward_bound. exact Hc.
  - intros c Hc. apply backward_bound, backward_bound. exact Hc.
  - intros c Hc. rewrite inverse_forward by (apply forward_bound; exact Hc).
    apply inverse_forward. exact Hc.
  - intros c Hc. rewrite inverse_backward by (apply backward_bound; exact Hc).
    apply inverse_backward. exact Hc.
  - intros l Hl. destruct (forward_lines inner l Hl) as [middle [Hm Hp]].
    destruct (forward_lines outer middle Hm) as [image [Hi Hq]].
    exists image. split; [exact Hi|]. rewrite <- map_map.
    eapply Permutation_trans; [apply Permutation_map; exact Hp|exact Hq].
  - intros l Hl. destruct (backward_lines outer l Hl) as [middle [Hm Hp]].
    destruct (backward_lines inner middle Hm) as [image [Hi Hq]].
    exists image. split; [exact Hi|]. rewrite <- map_map.
    eapply Permutation_trans; [apply Permutation_map; exact Hp|exact Hq].
Defined.

Definition coord_x (c : cell) := c mod 5.
Definition coord_y (c : cell) := (c / 5) mod 5.
Definition coord_z (c : cell) := c / 25.
Definition reflect_x (c : cell) := (4 - coord_x c) + 5 * coord_y c + 25 * coord_z c.
Definition reflect_y (c : cell) := coord_x c + 5 * (4 - coord_y c) + 25 * coord_z c.
Definition reflect_z (c : cell) := coord_x c + 5 * coord_y c + 25 * (4 - coord_z c).
Definition exchange_xy (c : cell) := coord_y c + 5 * coord_x c + 25 * coord_z c.
Definition exchange_yz (c : cell) := coord_x c + 5 * coord_z c + 25 * coord_y c.

Lemma reflect_x_check : isob reflect_x reflect_x = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reflect_y_check : isob reflect_y reflect_y = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reflect_z_check : isob reflect_z reflect_z = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exchange_xy_check : isob exchange_xy exchange_xy = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exchange_yz_check : isob exchange_yz exchange_yz = true.
Proof. vm_compute. reflexivity. Qed.

Definition rx := checked_iso reflect_x reflect_x reflect_x_check.
Definition ry := checked_iso reflect_y reflect_y reflect_y_check.
Definition rz := checked_iso reflect_z reflect_z reflect_z_check.
Definition sxy := checked_iso exchange_xy exchange_xy exchange_xy_check.
Definition syz := checked_iso exchange_yz exchange_yz exchange_yz_check.

Definition coordinate_permutations : list BoardIso :=
  [identity_iso; sxy; syz; compose_iso sxy syz; compose_iso syz sxy;
   compose_iso sxy (compose_iso syz sxy)].
Definition coordinate_reflections : list BoardIso :=
  [identity_iso; rx; ry; rz; compose_iso rx ry; compose_iso rx rz;
   compose_iso ry rz; compose_iso rx (compose_iso ry rz)].
Definition cube_symmetries : list BoardIso :=
  flat_map (fun permutation => map (compose_iso permutation) coordinate_reflections)
    coordinate_permutations.

Theorem cube_symmetries_count : length cube_symmetries = 48.
Proof. reflexivity. Qed.

Theorem cube_actions_distinct :
  NoDup (map (fun iso => map (forward iso) all_cells) cube_symmetries).
Proof. apply distinct_lines_sound. vm_compute. reflexivity. Qed.

Definition opening_representatives : list cell := [0;1;2;6;7;12;31;32;37;62].

Lemma opening_coverage_check :
  forallb (fun c => existsb (fun iso =>
    existsb (Nat.eqb (forward iso c)) opening_representatives) cube_symmetries) all_cells = true.
Proof. vm_compute. reflexivity. Qed.

Theorem every_opening_has_representative : forall c, c < 125 ->
  exists iso, In iso cube_symmetries /\ In (forward iso c) opening_representatives.
Proof.
  intros c Hc. pose proof opening_coverage_check as H.
  apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
  apply existsb_exists in H as [iso [Hi Hr]].
  exists iso. split; [exact Hi|apply member_spec; exact Hr].
Qed.

Definition opening_state (c : cell) : GameState := make_state [c] [] [c].
Definition opening_nonloss (c : cell) : Prop :=
  solve prevents_white false 124 false (opening_state c) = true.

Lemma opening_valid : forall c, c < 125 -> valid_state (opening_state c).
Proof.
  intros c Hc. constructor.
  - constructor; [exact Hc|constructor].
  - constructor; [intros H; contradiction|constructor].
  - reflexivity.
Qed.

Lemma one_white_stone_cannot_win : forall c, c < 125 -> has_win [c] = false.
Proof.
  intros c Hc.
  assert (Hcheck : forallb (fun c => negb (has_win [c])) all_cells = true) by reflexivity.
  apply forallb_forall with (x := c) in Hcheck; [apply negb_true_iff; exact Hcheck|apply in_seq; lia].
Qed.

Lemma effective_initial : forall c, c < 125 -> effective_move initial_state c = c.
Proof.
  intros c Hc. assert (Hlt : (c <? 125) = true) by (apply Nat.ltb_lt; exact Hc).
  assert (Hlegal : is_legal_move initial_state c = true).
  { unfold is_legal_move. rewrite Hlt. reflexivity. }
  unfold effective_move. rewrite Hlegal. reflexivity.
Qed.

Lemma opening_branch_value : forall request,
  branch prevents_white (solve prevents_white false 124) true initial_state request =
  solve prevents_white false 124 false (opening_state (effective_move initial_state request)).
Proof.
  intros request. set (e := effective_move initial_state request).
  assert (Hlegal : is_legal_move initial_state e = true)
    by (apply effective_move_is_legal; [apply initial_state_valid|cbn; lia]).
  destruct (legal_move_fresh initial_state e Hlegal) as [Hbound _].
  unfold branch at 1.
  change ((match move_result true (opening_state e) with
    | Some r => prevents_white r
    | None => solve prevents_white false 124 false (opening_state e)
    end) = solve prevents_white false 124 false (opening_state e)).
  assert (Hresult : move_result true (opening_state e) = None).
  { change ((if has_win [e] then Some WhiteWins else None) = None).
    exact (f_equal (fun won : bool => if won then Some WhiteWins else None)
      (one_white_stone_cannot_win e Hbound)). }
  rewrite Hresult. reflexivity.
Qed.

Theorem black_nonloss_iff_all_openings :
  Goal.BlackNonLossFromEmpty <-> forall c, c < 125 -> opening_nonloss c.
Proof.
  rewrite black_nonloss_iff_value. unfold black_nonloss_value.
  rewrite solve_successor.
  change (forallb (branch prevents_white (solve prevents_white false 124) true initial_state) requests = true
    <-> forall c, c < 125 -> opening_nonloss c).
  split.
  - intros H c Hc. apply forallb_forall with (x := c) in H; [|apply in_seq; lia].
    rewrite opening_branch_value, effective_initial in H by exact Hc. exact H.
  - intros H. apply forallb_forall. intros request Hin. rewrite opening_branch_value.
    apply H. pose proof (effective_move_is_legal initial_state request initial_state_valid ltac:(cbn; lia)) as Hlegal.
    destruct (legal_move_fresh initial_state _ Hlegal) as [Hbound _]. exact Hbound.
Qed.

Theorem all_openings_iff_ten_representatives :
  (forall c, c < 125 -> opening_nonloss c) <->
  (forall c, In c opening_representatives -> opening_nonloss c).
Proof.
  split.
  - intros H c Hc. apply H.
    assert (Hcheck : forallb (fun c => c <? 125) opening_representatives = true) by reflexivity.
    apply forallb_forall with (x := c) in Hcheck; [apply Nat.ltb_lt; exact Hcheck|exact Hc].
  - intros H c Hc.
    destruct (every_opening_has_representative c Hc) as [iso [Hi Hr]].
    pose proof (solve_symmetry iso prevents_white false 124 false (opening_state c)
      (opening_valid c Hc) eq_refl) as Hsym.
    change (solve prevents_white false 124 false (opening_state (forward iso c)) =
      solve prevents_white false 124 false (opening_state c)) in Hsym.
    unfold opening_nonloss. rewrite <- Hsym. apply H. exact Hr.
Qed.

Theorem black_nonloss_iff_ten_openings :
  Goal.BlackNonLossFromEmpty <->
  (forall c, In c opening_representatives -> opening_nonloss c).
Proof. rewrite black_nonloss_iff_all_openings. apply all_openings_iff_ten_representatives. Qed.

(** This equivalence isolates the actual remaining global obligations. None
    of the ten nonloss cases below is asserted to be proved by this module. *)
Theorem exact_draw_iff_ten_openings :
  Goal.ExactDraw <-> (forall c, In c opening_representatives -> opening_nonloss c).
Proof. rewrite exact_draw_iff_black_nonloss. apply black_nonloss_iff_ten_openings. Qed.

Definition ten_opening_check : bool :=
  forallb (fun c => solve prevents_white false 124 false (opening_state c)) opening_representatives.

Theorem exact_draw_iff_ten_opening_check : Goal.ExactDraw <-> ten_opening_check = true.
Proof.
  rewrite exact_draw_iff_ten_openings. unfold ten_opening_check.
  rewrite forallb_forall. reflexivity.
Qed.

Local Opaque black_nonloss_value ten_opening_check.

Theorem black_value_equals_ten_opening_check : black_nonloss_value = ten_opening_check.
Proof.
  destruct black_nonloss_value eqn:Hblack, ten_opening_check eqn:Hten; try reflexivity.
  - assert (Hdraw : Goal.ExactDraw).
    { apply exact_draw_iff_black_nonloss, black_nonloss_value_true. exact Hblack. }
    apply exact_draw_iff_ten_opening_check in Hdraw. congruence.
  - assert (Hdraw : Goal.ExactDraw) by (apply exact_draw_iff_ten_opening_check; exact Hten).
    destruct Hdraw as [Hnonloss _]. apply black_nonloss_iff_value in Hnonloss. congruence.
Qed.

Theorem white_forced_win_iff_ten_opening_check_false :
  WhiteForcedWin <-> ten_opening_check = false.
Proof.
  split.
  - intros [w Hw]. destruct ten_opening_check eqn:Hten; [|reflexivity].
    assert (Hdraw : Goal.ExactDraw) by (apply exact_draw_iff_ten_opening_check; exact Hten).
    destruct Hdraw as [[b Hb] _]. specialize (Hw b). specialize (Hb w). congruence.
  - intros Hten. apply black_nonloss_value_false.
    rewrite black_value_equals_ten_opening_check. exact Hten.
Qed.

Print Assumptions solve_symmetry.
Print Assumptions cube_actions_distinct.
Print Assumptions every_opening_has_representative.
Print Assumptions black_nonloss_iff_ten_openings.
Print Assumptions exact_draw_iff_ten_openings.
Print Assumptions exact_draw_iff_ten_opening_check.
Print Assumptions black_value_equals_ten_opening_check.
Print Assumptions white_forced_win_iff_ten_opening_check_false.
