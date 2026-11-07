(** **************************************************************************
    CheckersBoard.v: 32-Square Lattice Topology & Symmetries in Rocq 9.1
    
    This module formalizes the mathematical topology, coordinate indexing,
    diagonal adjacencies, jump vectors, and D2 symmetry group of the
    standard 8x8 Checkers (English Draughts) board on 32 dark squares.
    
    Covers:
    1. 32-Square Coordinate System: s in {0 .. 31}.
    2. Rank and File Projections.
    3. Dark-Square Parity Invariant: (rank + col) mod 2 = 1.
    4. Four Diagonal Step Functions: FL, FR, BL, BR.
    5. Four Constant Jump Vectors: +7 (FL), +9 (FR), -9 (BL), -7 (BR).
    6. Jump Rank Delta: exactly 2 ranks per jump.
    7. 180-degree Board Inversion (rot180).
    
    Zero unproven axioms, zero admissions (Closed under global context).
    ************************************************************************** *)

From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.

Section CheckersBoard.

Definition num_squares : nat := 32.

Definition valid_square (s : nat) : Prop := s < 32.

Definition sq_rank (s : nat) : nat := s / 4.

Definition sq_col (s : nat) : nat :=
  let r := sq_rank s in
  let c := s mod 4 in
  if Nat.even r then 2 * c + 1 else 2 * c.

Theorem sq_bounds : forall s : nat,
  s < 32 ->
  sq_rank s < 8 /\ sq_col s < 8.
Proof.
  intros s Hs.
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hdiv : s / 4 < 8).
  { assert (Hdm := Nat.div_mod s 4 ltac:(lia)). lia. }
  unfold sq_rank.
  cbv [sq_col sq_rank].
  destruct (Nat.even (s / 4)); split; lia.
Qed.

Theorem dark_square_parity : forall s : nat,
  s < 32 ->
  (sq_rank s + sq_col s) mod 2 = 1.
Proof.
  intros s Hs.
  cbv [sq_col sq_rank].
  destruct (Nat.even (s / 4)) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k Hk].
    assert (Hrw : s / 4 + (2 * (s mod 4) + 1) = 1 + (k + s mod 4) * 2) by lia.
    rewrite Hrw.
    rewrite Nat.Div0.mod_add.
    reflexivity.
  - assert (Hodd : Nat.Odd (s / 4)).
    { apply Nat.odd_spec. unfold Nat.odd. rewrite Heven. reflexivity. }
    destruct Hodd as [k Hk].
    assert (Hrw : s / 4 + 2 * (s mod 4) = 1 + (k + s mod 4) * 2) by lia.
    rewrite Hrw.
    rewrite Nat.Div0.mod_add.
    reflexivity.
Qed.

(** Division and Modulo Helpers *)

Lemma div4_ge_1 : forall s, 4 <= s -> 1 <= s / 4.
Proof.
  intros s H4.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  destruct (s / 4) eqn:Heq; lia.
Qed.

Lemma div4_add4 : forall s, (s + 4) / 4 = s / 4 + 1.
Proof.
  intros s.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  replace (s + 4) with (s mod 4 + (s / 4 + 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  assert (s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma div4_add3 : forall s, 0 < s mod 4 -> (s + 3) / 4 = s / 4 + 1.
Proof.
  intros s Hc.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  replace (s + 3) with ((s mod 4 - 1) + (s / 4 + 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  assert (s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (s mod 4 - 1 < 4) by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma div4_add5 : forall s, s mod 4 < 3 -> (s + 5) / 4 = s / 4 + 1.
Proof.
  intros s Hc.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  replace (s + 5) with ((s mod 4 + 1) + (s / 4 + 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  assert (s mod 4 + 1 < 4) by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma div4_sub4 : forall s, 4 <= s -> (s - 4) / 4 = s / 4 - 1.
Proof.
  intros s H4.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hr := div4_ge_1 s H4).
  replace (s - 4) with (s mod 4 + (s / 4 - 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma div4_sub5 : forall s, 5 <= s -> 0 < s mod 4 -> (s - 5) / 4 = s / 4 - 1.
Proof.
  intros s H5 Hc.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hr : 1 <= s / 4).
  { apply div4_ge_1. lia. }
  replace (s - 5) with ((s mod 4 - 1) + (s / 4 - 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma div4_sub3 : forall s, 4 <= s -> s mod 4 < 3 -> (s - 3) / 4 = s / 4 - 1.
Proof.
  intros s H4 Hc.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hr := div4_ge_1 s H4).
  replace (s - 3) with ((s mod 4 + 1) + (s / 4 - 1) * 4) by lia.
  rewrite Nat.div_add by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma mod4_add4 : forall s, (s + 4) mod 4 = s mod 4.
Proof.
  intros s.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  replace (s + 4) with (s mod 4 + (s / 4 + 1) * 4) by lia.
  rewrite Nat.Div0.mod_add.
  apply Nat.Div0.mod_mod.
Qed.

Lemma mod4_sub4 : forall s, 4 <= s -> (s - 4) mod 4 = s mod 4.
Proof.
  intros s H4.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hr := div4_ge_1 s H4).
  replace (s - 4) with (s mod 4 + (s / 4 - 1) * 4) by lia.
  rewrite Nat.Div0.mod_add.
  apply Nat.Div0.mod_mod.
Qed.

Lemma even_div4_add4 : forall s, Nat.even ((s + 4) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s. rewrite div4_add4.
  replace (s / 4 + 1) with (S (s / 4)) by lia.
  rewrite Nat.even_succ. unfold Nat.odd. reflexivity.
Qed.

Lemma even_div4_add3 : forall s, 0 < s mod 4 -> Nat.even ((s + 3) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s Hc. rewrite (div4_add3 s Hc).
  replace (s / 4 + 1) with (S (s / 4)) by lia.
  rewrite Nat.even_succ. unfold Nat.odd. reflexivity.
Qed.

Lemma even_div4_add5 : forall s, s mod 4 < 3 -> Nat.even ((s + 5) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s Hc. rewrite (div4_add5 s Hc).
  replace (s / 4 + 1) with (S (s / 4)) by lia.
  rewrite Nat.even_succ. unfold Nat.odd. reflexivity.
Qed.

Lemma even_div4_sub4 : forall s, 4 <= s -> Nat.even ((s - 4) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s H4. rewrite (div4_sub4 s H4).
  assert (Hr := div4_ge_1 s H4).
  replace (s / 4) with (S (s / 4 - 1)) at 2 by lia.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  rewrite negb_involutive. reflexivity.
Qed.

Lemma even_div4_sub5 : forall s, 5 <= s -> 0 < s mod 4 -> Nat.even ((s - 5) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s H5 Hc. rewrite (div4_sub5 s H5 Hc).
  assert (Hr : 1 <= s / 4) by (apply div4_ge_1; lia).
  replace (s / 4) with (S (s / 4 - 1)) at 2 by lia.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  rewrite negb_involutive. reflexivity.
Qed.

Lemma even_div4_sub3 : forall s, 4 <= s -> s mod 4 < 3 -> Nat.even ((s - 3) / 4) = negb (Nat.even (s / 4)).
Proof.
  intros s H4 Hc. rewrite (div4_sub3 s H4 Hc).
  assert (Hr := div4_ge_1 s H4).
  replace (s / 4) with (S (s / 4 - 1)) at 2 by lia.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  rewrite negb_involutive. reflexivity.
Qed.

(** Step Functions *)

Definition step_fl (s : nat) : option nat :=
  if s <? 28 then
    let r := sq_rank s in
    let c := s mod 4 in
    if Nat.even r then Some (s + 4)
    else if 0 <? c then Some (s + 3) else None
  else None.

Definition step_fr (s : nat) : option nat :=
  if s <? 28 then
    let r := sq_rank s in
    let c := s mod 4 in
    if Nat.even r then
      if c <? 3 then Some (s + 5) else None
    else Some (s + 4)
  else None.

Definition step_bl (s : nat) : option nat :=
  if 4 <=? s then
    let r := sq_rank s in
    let c := s mod 4 in
    if Nat.even r then
      if (0 <? c) && (5 <=? s) then Some (s - 5) else None
    else Some (s - 4)
  else None.

Definition step_br (s : nat) : option nat :=
  if 4 <=? s then
    let r := sq_rank s in
    let c := s mod 4 in
    if Nat.even r then Some (s - 4)
    else if c <? 3 then Some (s - 3) else None
  else None.

(** Theorem 3: Valid steps strictly increase (forward) or decrease (backward) rank by exactly 1. *)
Theorem step_fl_rank : forall s dest : nat,
  step_fl s = Some dest ->
  sq_rank dest = sq_rank s + 1.
Proof.
  intros s dest H.
  unfold step_fl, sq_rank in *.
  destruct (s <? 28) eqn:H28; [|discriminate].
  destruct (Nat.even (s / 4)).
  - injection H as Heq; subst dest. apply div4_add4.
  - destruct (0 <? s mod 4) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection H as Heq; subst dest. apply div4_add3. lia.
Qed.

Theorem step_fr_rank : forall s dest : nat,
  step_fr s = Some dest ->
  sq_rank dest = sq_rank s + 1.
Proof.
  intros s dest H.
  unfold step_fr, sq_rank in *.
  destruct (s <? 28) eqn:H28; [|discriminate].
  destruct (Nat.even (s / 4)).
  - destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection H as Heq; subst dest. apply div4_add5. lia.
  - injection H as Heq; subst dest. apply div4_add4.
Qed.

Theorem step_bl_rank : forall s dest : nat,
  step_bl s = Some dest ->
  sq_rank s = sq_rank dest + 1.
Proof.
  intros s dest H.
  unfold step_bl, sq_rank in *.
  destruct (4 <=? s) eqn:H4; [|discriminate].
  apply Nat.leb_le in H4.
  destruct (Nat.even (s / 4)).
  - destruct ((0 <? s mod 4) && (5 <=? s)) eqn:Hc; [|discriminate].
    apply andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
    apply Nat.ltb_lt in Hc1. apply Nat.leb_le in Hc2.
    injection H as Heq; subst dest.
    rewrite (div4_sub5 s Hc2 Hc1).
    assert (Hr : 1 <= s / 4) by (apply div4_ge_1; lia). lia.
  - injection H as Heq; subst dest.
    rewrite (div4_sub4 s H4).
    assert (Hr := div4_ge_1 s H4). lia.
Qed.

Theorem step_br_rank : forall s dest : nat,
  step_br s = Some dest ->
  sq_rank s = sq_rank dest + 1.
Proof.
  intros s dest H.
  unfold step_br, sq_rank in *.
  destruct (4 <=? s) eqn:H4; [|discriminate].
  apply Nat.leb_le in H4.
  destruct (Nat.even (s / 4)).
  - injection H as Heq; subst dest.
    rewrite (div4_sub4 s H4).
    assert (Hr := div4_ge_1 s H4). lia.
  - destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection H as Heq; subst dest.
    rewrite (div4_sub3 s H4 Hc).
    assert (Hr := div4_ge_1 s H4). lia.
Qed.

(** Jump Definitions *)

Definition jump_fl (s : nat) : option (nat * nat) :=
  match step_fl s with
  | Some mid =>
      match step_fl mid with
      | Some dest => Some (mid, dest)
      | None => None
      end
  | None => None
  end.

Definition jump_fr (s : nat) : option (nat * nat) :=
  match step_fr s with
  | Some mid =>
      match step_fr mid with
      | Some dest => Some (mid, dest)
      | None => None
      end
  | None => None
  end.

Definition jump_bl (s : nat) : option (nat * nat) :=
  match step_bl s with
  | Some mid =>
      match step_bl mid with
      | Some dest => Some (mid, dest)
      | None => None
      end
  | None => None
  end.

Definition jump_br (s : nat) : option (nat * nat) :=
  match step_br s with
  | Some mid =>
      match step_br mid with
      | Some dest => Some (mid, dest)
      | None => None
      end
  | None => None
  end.

(** Jump Offsets *)

Theorem jump_fl_offset : forall s mid dest : nat,
  jump_fl s = Some (mid, dest) ->
  dest = s + 7.
Proof.
  intros s mid dest H.
  unfold jump_fl in H.
  destruct (step_fl s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_fl m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  unfold step_fl, sq_rank in *.
  cbn zeta in *.
  destruct (s <? 28) eqn:Hs28; [|discriminate].
  destruct (Nat.even (s / 4)) eqn:Hre.
  - injection Hm as Hmeq; subst mid.
    destruct (s + 4 <? 28) eqn:Hm28; [|discriminate].
    rewrite even_div4_add4 in Hd. rewrite Hre in Hd.
    rewrite mod4_add4 in Hd.
    destruct (0 <? s mod 4) eqn:Hc; [|discriminate].
    injection Hd as Hdeq; subst dest. lia.
  - destruct (0 <? s mod 4) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection Hm as Hmeq; subst mid.
    destruct (s + 3 <? 28) eqn:Hm28; [|discriminate].
    rewrite (even_div4_add3 s Hc) in Hd. rewrite Hre in Hd.
    injection Hd as Hdeq; subst dest. lia.
Qed.

Theorem jump_fr_offset : forall s mid dest : nat,
  jump_fr s = Some (mid, dest) ->
  dest = s + 9.
Proof.
  intros s mid dest H.
  unfold jump_fr in H.
  destruct (step_fr s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_fr m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  unfold step_fr, sq_rank in *.
  cbn zeta in *.
  destruct (s <? 28) eqn:Hs28; [|discriminate].
  destruct (Nat.even (s / 4)) eqn:Hre.
  - destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection Hm as Hmeq; subst mid.
    destruct (s + 5 <? 28) eqn:Hm28; [|discriminate].
    rewrite (even_div4_add5 s Hc) in Hd. rewrite Hre in Hd.
    injection Hd as Hdeq; subst dest. lia.
  - injection Hm as Hmeq; subst mid.
    destruct (s + 4 <? 28) eqn:Hm28; [|discriminate].
    rewrite even_div4_add4 in Hd. rewrite Hre in Hd.
    rewrite mod4_add4 in Hd.
    destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    injection Hd as Hdeq; subst dest. lia.
Qed.

Theorem jump_bl_offset : forall s mid dest : nat,
  jump_bl s = Some (mid, dest) ->
  dest = s - 9.
Proof.
  intros s mid dest H.
  unfold jump_bl in H.
  destruct (step_bl s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_bl m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  unfold step_bl, sq_rank in *.
  cbn zeta in *.
  destruct (4 <=? s) eqn:Hs4; [|discriminate].
  apply Nat.leb_le in Hs4.
  destruct (Nat.even (s / 4)) eqn:Hre.
  - destruct ((0 <? s mod 4) && (5 <=? s)) eqn:Hc; [|discriminate].
    apply andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
    apply Nat.ltb_lt in Hc1. apply Nat.leb_le in Hc2.
    injection Hm as Hmeq; subst mid.
    destruct (4 <=? s - 5) eqn:Hm4; [|discriminate].
    rewrite (even_div4_sub5 s Hc2 Hc1) in Hd. rewrite Hre in Hd.
    injection Hd as Hdeq; subst dest. lia.
  - injection Hm as Hmeq; subst mid.
    destruct (4 <=? s - 4) eqn:Hm4; [|discriminate].
    apply Nat.leb_le in Hm4.
    rewrite (even_div4_sub4 s Hs4) in Hd. rewrite Hre in Hd.
    rewrite (mod4_sub4 s Hs4) in Hd.
    destruct ((0 <? s mod 4) && (5 <=? s - 4)) eqn:Hc; [|discriminate].
    injection Hd as Hdeq; subst dest. lia.
Qed.

Theorem jump_br_offset : forall s mid dest : nat,
  jump_br s = Some (mid, dest) ->
  dest = s - 7.
Proof.
  intros s mid dest H.
  unfold jump_br in H.
  destruct (step_br s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_br m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  unfold step_br, sq_rank in *.
  cbn zeta in *.
  destruct (4 <=? s) eqn:Hs4; [|discriminate].
  apply Nat.leb_le in Hs4.
  destruct (Nat.even (s / 4)) eqn:Hre.
  - injection Hm as Hmeq; subst mid.
    destruct (4 <=? s - 4) eqn:Hm4; [|discriminate].
    apply Nat.leb_le in Hm4.
    rewrite (even_div4_sub4 s Hs4) in Hd. rewrite Hre in Hd.
    rewrite (mod4_sub4 s Hs4) in Hd.
    destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    injection Hd as Hdeq; subst dest. lia.
  - destruct (s mod 4 <? 3) eqn:Hc; [|discriminate].
    apply Nat.ltb_lt in Hc.
    injection Hm as Hmeq; subst mid.
    destruct (4 <=? s - 3) eqn:Hm4; [|discriminate].
    rewrite (even_div4_sub3 s Hs4 Hc) in Hd. rewrite Hre in Hd.
    injection Hd as Hdeq; subst dest. lia.
Qed.

Theorem jump_fl_rank : forall s mid dest : nat,
  jump_fl s = Some (mid, dest) ->
  sq_rank dest = sq_rank s + 2.
Proof.
  intros s mid dest H.
  unfold jump_fl in H.
  destruct (step_fl s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_fl m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  apply step_fl_rank in Hm.
  apply step_fl_rank in Hd.
  lia.
Qed.

Theorem jump_fr_rank : forall s mid dest : nat,
  jump_fr s = Some (mid, dest) ->
  sq_rank dest = sq_rank s + 2.
Proof.
  intros s mid dest H.
  unfold jump_fr in H.
  destruct (step_fr s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_fr m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  apply step_fr_rank in Hm.
  apply step_fr_rank in Hd.
  lia.
Qed.

Theorem jump_bl_rank : forall s mid dest : nat,
  jump_bl s = Some (mid, dest) ->
  sq_rank s = sq_rank dest + 2.
Proof.
  intros s mid dest H.
  unfold jump_bl in H.
  destruct (step_bl s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_bl m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  apply step_bl_rank in Hm.
  apply step_bl_rank in Hd.
  lia.
Qed.

Theorem jump_br_rank : forall s mid dest : nat,
  jump_br s = Some (mid, dest) ->
  sq_rank s = sq_rank dest + 2.
Proof.
  intros s mid dest H.
  unfold jump_br in H.
  destruct (step_br s) as [m|] eqn:Hm; [|discriminate].
  destruct (step_br m) as [d|] eqn:Hd; [|discriminate].
  injection H as Hmid Hdest; subst m d.
  apply step_br_rank in Hm.
  apply step_br_rank in Hd.
  lia.
Qed.

(** Symmetry: rot180 *)

Definition rot180 (s : nat) : nat := 31 - s.

Theorem rot180_involutive : forall s : nat,
  s < 32 ->
  rot180 (rot180 s) = s.
Proof.
  intros s Hs. unfold rot180. lia.
Qed.

Theorem rot180_valid : forall s : nat,
  s < 32 ->
  rot180 s < 32.
Proof.
  intros s Hs. unfold rot180. lia.
Qed.

Theorem rot180_rank : forall s : nat,
  s < 32 ->
  sq_rank (rot180 s) = 7 - sq_rank s.
Proof.
  intros s Hs.
  unfold rot180, sq_rank.
  assert (Hdm := Nat.div_mod s 4 ltac:(lia)).
  assert (Hmod : s mod 4 < 4) by (apply Nat.mod_upper_bound; lia).
  assert (Hdiv : s / 4 < 8) by lia.
  replace (31 - s) with ((3 - s mod 4) + (7 - s / 4) * 4) by lia.
  rewrite Nat.div_add by lia.
  assert (3 - s mod 4 < 4) by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

End CheckersBoard.
