(** C5Pairing9x7.v: The 31-Pair Static Transversal Partition for 9x7 Connect-5 **)
From Stdlib Require Import List Arith Lia Bool.
From C5_9x7 Require Import C5Board9x7.
Import ListNotations.

(** The 4 Base-Row Symmetric Horizontal Cross-Pairs (Row 0) **)
Definition base_pairs : list (cell * cell) :=
  [ ((3, 0), (5, 0));
    ((2, 0), (6, 0));
    ((1, 0), (7, 0));
    ((0, 0), (8, 0)) ].

(** The 3 Center-Axis Vertical Dominoes (Column 4, Rows 1..6) **)
Definition center_pairs : list (cell * cell) :=
  [ ((4, 1), (4, 2));
    ((4, 3), (4, 4));
    ((4, 5), (4, 6)) ].

(** The 24 Wing Vertical Dominoes (Columns {0,1,2,3,5,6,7,8}, Rows 1..6) **)
Definition wing_col_pairs (c : nat) : list (cell * cell) :=
  [ ((c, 1), (c, 2));
    ((c, 3), (c, 4));
    ((c, 5), (c, 6)) ].

Definition wing_pairs : list (cell * cell) :=
  wing_col_pairs 0 ++ wing_col_pairs 1 ++ wing_col_pairs 2 ++ wing_col_pairs 3 ++
  wing_col_pairs 5 ++ wing_col_pairs 6 ++ wing_col_pairs 7 ++ wing_col_pairs 8.

(** The Complete 31-Pair Partition of the 62 Non-Opening Cells **)
Definition all_31_pairs : list (cell * cell) :=
  base_pairs ++ center_pairs ++ wing_pairs.

(** Theorem: Exact Pair Count **)
Theorem pair_count_is_31 : length all_31_pairs = 31.
Proof. vm_compute. reflexivity. Qed.

(** Partner Lookup Function **)
Definition partner (xy : cell) : option cell :=
  let '(c, r) := xy in
  if Nat.eqb c 4 then
    match r with
    | 0 => None (* Opening move of White *)
    | 1 => Some (4, 2)
    | 2 => Some (4, 1)
    | 3 => Some (4, 4)
    | 4 => Some (4, 3)
    | 5 => Some (4, 6)
    | 6 => Some (4, 5)
    | _ => None
    end
  else if Nat.eqb r 0 then
    match c with
    | 0 => Some (8, 0)
    | 1 => Some (7, 0)
    | 2 => Some (6, 0)
    | 3 => Some (5, 0)
    | 5 => Some (3, 0)
    | 6 => Some (2, 0)
    | 7 => Some (1, 0)
    | 8 => Some (0, 0)
    | _ => None
    end
  else if (c <? 9) && (r <? 7) then
    match r with
    | 1 => Some (c, 2)
    | 2 => Some (c, 1)
    | 3 => Some (c, 4)
    | 4 => Some (c, 3)
    | 5 => Some (c, 6)
    | 6 => Some (c, 5)
    | _ => None
    end
  else None.

(** Theorem: Opening Move has No Partner **)
Theorem opening_move_unpaired : partner (4, 0) = None.
Proof. vm_compute. reflexivity. Qed.

(** Theorem: Partner is Involutive for All Valid Non-Opening Cells **)
Theorem partner_involutive :
  forall c r,
    c < 9 -> r < 7 ->
    (c = 4 /\ r = 0 -> False) ->
    match partner (c, r) with
    | Some p => partner p = Some (c, r)
    | None => False
    end.
Proof.
  intros c r Hc Hr Hnot_op.
  do 9 (destruct c as [|c]; [
    do 7 (destruct r as [|r]; [
      vm_compute; try reflexivity; exfalso; apply Hnot_op; split; reflexivity |]);
    lia |]).
  lia.
Qed.

(** Theorem: Partner is Always Distinct (No Self-Pairing) **)
Theorem partner_distinct :
  forall c r p,
    partner (c, r) = Some p ->
    (c, r) <> p.
Proof.
  intros c r p Hpart Heq.
  subst.
  destruct (c <? 9) eqn:Hc.
  - destruct (r <? 7) eqn:Hr.
    + apply Nat.ltb_lt in Hc.
      apply Nat.ltb_lt in Hr.
      do 9 (destruct c as [|c]; [
        do 7 (destruct r as [|r]; [
          inversion Hpart; subst; discriminate |]);
        lia |]); lia.
    + unfold partner in Hpart.
      destruct (c =? 4).
      * destruct r as [|[|[|[|[|[|[|?]]]]]]]; inversion Hpart; subst; discriminate.
      * destruct (r =? 0).
        -- destruct c as [|[|[|[|[|[|[|[|[|?]]]]]]]]]; inversion Hpart; subst; discriminate.
        -- rewrite Hr in Hpart; rewrite andb_false_r in Hpart; discriminate.
  - unfold partner in Hpart.
    destruct (c =? 4) eqn:Ec.
    * apply Nat.eqb_eq in Ec; subst; discriminate.
    * destruct (r =? 0).
      -- destruct c as [|[|[|[|[|[|[|[|[|?]]]]]]]]]; inversion Hpart; subst; discriminate.
      -- rewrite Hc in Hpart; simpl in Hpart; discriminate.
Qed.

(** Theorem: Partner Preserves Validity **)
Theorem partner_valid :
  forall c r p,
    c < 9 -> r < 7 ->
    partner (c, r) = Some p ->
    cell_valid p = true.
Proof.
  intros c r p Hc Hr Hpart.
  do 9 (destruct c as [|c]; [
    do 7 (destruct r as [|r]; [
      inversion Hpart; subst; vm_compute; reflexivity |]);
    lia |]).
  lia.
Qed.

(** Theorem: Symmetric Cross-Pairs Respect Reflection Axis **)
Theorem base_pairs_symmetric :
  forall c, c < 4 -> partner (c, 0) = Some (refl_c c, 0).
Proof.
  intros c Hc.
  repeat (destruct c as [|c]; [vm_compute; reflexivity|]); lia.
Qed.

(** Theorem: The Opening Move (4, 0) is the ONLY Valid Cell with partner = None **)
Theorem partner_none_is_4_0 :
  forall c r,
    c < 9 -> r < 7 ->
    partner (c, r) = None ->
    (c, r) = (4, 0).
Proof.
  intros c r Hc Hr Hpart.
  unfold partner in Hpart.
  destruct (c =? 4) eqn:Ec.
  - apply Nat.eqb_eq in Ec; subst.
    destruct r as [|[|[|[|[|[|[|?]]]]]]]; [reflexivity | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | lia].
  - destruct (r =? 0) eqn:Er.
    + apply Nat.eqb_eq in Er; subst.
      destruct c as [|[|[|[|[|[|[|[|[|?]]]]]]]]]; [discriminate | discriminate | discriminate | discriminate | idtac | discriminate | discriminate | discriminate | discriminate | lia].
      apply Nat.eqb_neq in Ec. exfalso. apply Ec. reflexivity.
    + assert (Hc9 : (c <? 9) = true) by (apply Nat.ltb_lt; auto).
      assert (Hr7 : (r <? 7) = true) by (apply Nat.ltb_lt; auto).
      rewrite Hc9, Hr7 in Hpart; simpl in Hpart.
      destruct r as [|[|[|[|[|[|[|?]]]]]]]; [idtac | discriminate | discriminate | discriminate | discriminate | discriminate | discriminate | lia].
      apply Nat.eqb_neq in Er. exfalso. apply Er. reflexivity.
Qed.
