(** * MNKHalesJewett.v: Every (m, n, k) Game with k >= 9 is a Draw

    Hales and Jewett (1963): nine in a row can never be forced, on any board.
    The proof is a single pairing of the plane with period 8.  The plane is
    tiled by dominoes in the four line directions so that every row, column,
    diagonal and anti-diagonal carries exactly one domino of its own
    direction in every 8 consecutive cells.  Any 9 consecutive cells of a line
    then contain a whole domino, and the opponent answers every move in the
    partner cell.

    The 8 x 8 tile, found by an exact-cover search
    (solver/hales_jewett_tile.py); a domino joins the two ends shown:

      H< H> V^ V^ V^ V^ V^ V^         H< H>   horizontal: (r, c) - (r, c + 1)
      H< H> Vv Vv Vv Vv Vv Vv         V^ Vv   vertical:   (r, c) - (r + 1, c)
      H< H> A^ A^ A^ D^ D^ D^         D^ Dv   diagonal:   (r, c) - (r + 1, c + 1)
      Dv Av Av Av H< H> Dv Dv         A^ Av   anti-diag.: (r, c) - (r + 1, c - 1)
      V^ V^ D^ A^ H< H> D^ A^
      Vv Vv Av Dv H< H> Av Dv
      H< H> A^ A^ A^ D^ D^ D^
      Dv Av Av Av H< H> Dv Dv

    On a finite board, a cell whose partner falls outside the board stays
    unpaired; no line of the board needs it.  Every property of the tile is
    checked by computation over one period ([hj_tile_consistent],
    [hj_tile_lines]) and lifted to all boards by arithmetic modulo 8.

    Main results:
      - [mnk_hales_jewett_breaker_wins]: in the Maker-Breaker game with
        k >= 9, Breaker wins on every board, whoever moves first.
      - [mnk_hales_jewett_draw]: every (m, n, k) game with k >= 9 is a draw.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame MNKPairing MNKErdosSelfridge MNKMakerBreaker.

(* ========================================================================= *)
(** * 1. The tile and the pairing                                            *)
(* ========================================================================= *)

(** Cell kinds:
      0  left end of a horizontal domino       partner (r, c + 1)
      1  right end                             partner (r, c - 1)
      2  top end of a vertical domino          partner (r + 1, c)
      3  bottom end                            partner (r - 1, c)
      4  top end of a diagonal domino          partner (r + 1, c + 1)
      5  bottom end                            partner (r - 1, c - 1)
      6  top end of an anti-diagonal domino    partner (r + 1, c - 1)
      7  bottom end                            partner (r - 1, c + 1) *)
Definition hj_table : list nat :=
  [0; 1; 2; 2; 2; 2; 2; 2;
   0; 1; 3; 3; 3; 3; 3; 3;
   0; 1; 6; 6; 6; 4; 4; 4;
   5; 7; 7; 7; 0; 1; 5; 5;
   2; 2; 4; 6; 0; 1; 4; 6;
   3; 3; 7; 5; 0; 1; 7; 5;
   0; 1; 6; 6; 6; 4; 4; 4;
   5; 7; 7; 7; 0; 1; 5; 5].

Definition hj_tile (rho gamma : nat) : nat := nth (8 * rho + gamma) hj_table 0.

Definition hj_kind (r c : nat) : nat := hj_tile (r mod 8) (c mod 8).

(** The partner of cell [x] = (r, c) of the m x n board, or [x] itself when
    the partner lies outside the board. *)
Definition hj_step (m n r c x : nat) : nat :=
  match hj_kind r c with
  | 0 => if c + 1 <? n then r * n + (c + 1) else x
  | 1 => if 1 <=? c then r * n + (c - 1) else x
  | 2 => if r + 1 <? m then (r + 1) * n + c else x
  | 3 => if 1 <=? r then (r - 1) * n + c else x
  | 4 => if (r + 1 <? m) && (c + 1 <? n) then (r + 1) * n + (c + 1) else x
  | 5 => if (1 <=? r) && (1 <=? c) then (r - 1) * n + (c - 1) else x
  | 6 => if (r + 1 <? m) && (1 <=? c) then (r + 1) * n + (c - 1) else x
  | _ => if (1 <=? r) && (c + 1 <? n) then (r - 1) * n + (c + 1) else x
  end.

Definition hj_partner (m n x : nat) : nat := hj_step m n (x / n) (x mod n) x.

Lemma hj_partner_rc : forall m n r c, c < n ->
  hj_partner m n (r * n + c) = hj_step m n r c (r * n + c).
Proof. intros m n r c Hc. unfold hj_partner. rewrite idx_div, idx_mod by exact Hc. reflexivity. Qed.

(* ========================================================================= *)
(** * 2. Finite checks over one period                                       *)
(* ========================================================================= *)

Definition all_residues (f : nat -> nat -> bool) : bool :=
  forallb (fun rho => forallb (f rho) (seq 0 8)) (seq 0 8).

Lemma all_residues_spec : forall f r c,
  all_residues f = true -> f (r mod 8) (c mod 8) = true.
Proof.
  intros f r c H. unfold all_residues in H. rewrite forallb_forall in H.
  assert (Hr : In (r mod 8) (seq 0 8)).
  { apply in_seq. pose proof (Nat.mod_upper_bound r 8 ltac:(lia)). lia. }
  specialize (H _ Hr). rewrite forallb_forall in H. apply H.
  apply in_seq. pose proof (Nat.mod_upper_bound c 8 ltac:(lia)). lia.
Qed.

(** Each end of a domino sees the other end, with the opposite kind. *)
Definition hj_tile_ok (rho gamma : nat) : bool :=
  match hj_tile rho gamma with
  | 0 => hj_tile rho ((gamma + 1) mod 8) =? 1
  | 1 => hj_tile rho ((gamma + 7) mod 8) =? 0
  | 2 => hj_tile ((rho + 1) mod 8) gamma =? 3
  | 3 => hj_tile ((rho + 7) mod 8) gamma =? 2
  | 4 => hj_tile ((rho + 1) mod 8) ((gamma + 1) mod 8) =? 5
  | 5 => hj_tile ((rho + 7) mod 8) ((gamma + 7) mod 8) =? 4
  | 6 => hj_tile ((rho + 1) mod 8) ((gamma + 7) mod 8) =? 7
  | _ => hj_tile ((rho + 7) mod 8) ((gamma + 1) mod 8) =? 6
  end.

Lemma hj_tile_consistent : all_residues hj_tile_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** Every 8 consecutive cells of a line, starting anywhere, contain the first
    end of a domino of the line's own direction.  An anti-diagonal is walked
    from its top-right cell, so its columns decrease. *)
Definition hj_has_h (rho gamma : nat) : bool :=
  existsb (fun j => hj_tile rho ((gamma + j) mod 8) =? 0) (seq 0 8).

Definition hj_has_v (rho gamma : nat) : bool :=
  existsb (fun j => hj_tile ((rho + j) mod 8) gamma =? 2) (seq 0 8).

Definition hj_has_d (rho gamma : nat) : bool :=
  existsb (fun j => hj_tile ((rho + j) mod 8) ((gamma + j) mod 8) =? 4) (seq 0 8).

Definition hj_has_a (rho gamma : nat) : bool :=
  existsb (fun t => hj_tile ((rho + t) mod 8) ((gamma + (8 - t)) mod 8) =? 6) (seq 0 8).

Lemma hj_tile_lines :
  all_residues (fun rho gamma =>
    hj_has_h rho gamma && hj_has_v rho gamma && hj_has_d rho gamma && hj_has_a rho gamma)
  = true.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(** * 3. Arithmetic modulo 8                                                 *)
(* ========================================================================= *)

Lemma mod8_add : forall a b, (a + b) mod 8 = (a mod 8 + b) mod 8.
Proof. intros a b. symmetry. apply Nat.Div0.add_mod_idemp_l. Qed.

Lemma mod8_sub : forall a b, b <= a -> b <= 8 -> (a - b) mod 8 = (a mod 8 + (8 - b)) mod 8.
Proof.
  intros a b Hba Hb. rewrite <- mod8_add.
  rewrite <- (Nat.Div0.mod_add (a - b) 1 8). f_equal. lia.
Qed.

Lemma mod8_pred : forall a, 1 <= a -> (a - 1) mod 8 = (a mod 8 + 7) mod 8.
Proof. intros a Ha. exact (mod8_sub a 1 Ha ltac:(lia)). Qed.

(** The consistency check, read on actual cells. *)
Lemma hj_kind_ok : forall r c,
  match hj_kind r c with
  | 0 => hj_kind r (c + 1) = 1
  | 1 => 1 <= c -> hj_kind r (c - 1) = 0
  | 2 => hj_kind (r + 1) c = 3
  | 3 => 1 <= r -> hj_kind (r - 1) c = 2
  | 4 => hj_kind (r + 1) (c + 1) = 5
  | 5 => 1 <= r -> 1 <= c -> hj_kind (r - 1) (c - 1) = 4
  | 6 => 1 <= c -> hj_kind (r + 1) (c - 1) = 7
  | _ => 1 <= r -> hj_kind (r - 1) (c + 1) = 6
  end.
Proof.
  intros r c. pose proof (all_residues_spec _ r c hj_tile_consistent) as H.
  unfold hj_tile_ok in H. revert H. unfold hj_kind at 1.
  destruct (hj_tile (r mod 8) (c mod 8)) as [|[|[|[|[|[|[|k]]]]]]];
    cbv beta iota; intros H; apply Nat.eqb_eq in H; intros; unfold hj_kind;
    rewrite ?(mod8_add r 1), ?(mod8_add c 1);
    rewrite ?mod8_pred by assumption;
    exact H.
Qed.

(* ========================================================================= *)
(** * 4. The pairing is an involution of the board                          *)
(* ========================================================================= *)

Ltac hj_bools :=
  repeat match goal with
  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Nat.leb_spec a b)
  end;
  cbn [andb].

Lemma hj_idx_lt : forall m n r c, r < m -> c < n -> r * n + c < m * n.
Proof. intros m n r c Hr Hc. nia. Qed.

Lemma hj_invol_rc : forall m n r c, r < m -> c < n ->
  hj_partner m n (hj_step m n r c (r * n + c)) = r * n + c.
Proof.
  intros m n r c Hr Hc. pose proof (hj_kind_ok r c) as Hok. revert Hok.
  unfold hj_step at 1.
  destruct (hj_kind r c) as [|[|[|[|[|[|[|k]]]]]]] eqn:Ek;
    cbv beta iota; intros Hok; hj_bools;
    rewrite hj_partner_rc by lia; unfold hj_step;
    first [ rewrite Ek | rewrite Hok by lia ];
    cbv beta iota; hj_bools;
    rewrite ?Nat.add_sub; rewrite ?Nat.sub_add by lia;
    first [ reflexivity | lia ].
Qed.

Lemma hj_range_rc : forall m n r c, r < m -> c < n ->
  hj_step m n r c (r * n + c) < m * n.
Proof.
  intros m n r c Hr Hc. unfold hj_step.
  destruct (hj_kind r c) as [|[|[|[|[|[|[|k]]]]]]]; cbv beta iota; hj_bools;
    apply hj_idx_lt; lia.
Qed.

Lemma hj_decompose : forall m n x, x < m * n ->
  n <> 0 /\ x / n < m /\ x mod n < n /\ x = x / n * n + x mod n.
Proof.
  intros m n x Hx.
  assert (Hn : n <> 0) by (intros ->; lia).
  split; [exact Hn |]. split; [apply Nat.Div0.div_lt_upper_bound; lia |].
  split; [apply Nat.mod_upper_bound; exact Hn |].
  rewrite (Nat.div_mod_eq x n) at 1. rewrite Nat.mul_comm. reflexivity.
Qed.

Theorem hj_partner_invol : forall m n x, x < m * n ->
  hj_partner m n (hj_partner m n x) = x.
Proof.
  intros m n x Hx. destruct (hj_decompose m n x Hx) as (_ & Hr & Hc & Hxe).
  rewrite Hxe. rewrite (hj_partner_rc m n (x / n) (x mod n) Hc).
  apply hj_invol_rc; assumption.
Qed.

Theorem hj_partner_range : forall m n x, x < m * n -> hj_partner m n x < m * n.
Proof.
  intros m n x Hx. destruct (hj_decompose m n x Hx) as (_ & Hr & Hc & Hxe).
  rewrite Hxe. rewrite (hj_partner_rc m n (x / n) (x mod n) Hc).
  apply hj_range_rc; assumption.
Qed.

(* ========================================================================= *)
(** * 5. Every line of length at least 9 contains a pair                    *)
(* ========================================================================= *)

Lemma hj_window_h : forall r c, exists j, j < 8 /\ hj_kind r (c + j) = 0.
Proof.
  intros r c. pose proof (all_residues_spec _ r c hj_tile_lines) as H. cbv beta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  unfold hj_has_h in H. apply existsb_exists in H as [j [Hj Ht]].
  apply in_seq in Hj. apply Nat.eqb_eq in Ht.
  exists j. split; [lia |]. unfold hj_kind. rewrite (mod8_add c j). exact Ht.
Qed.

Lemma hj_window_v : forall r c, exists j, j < 8 /\ hj_kind (r + j) c = 2.
Proof.
  intros r c. pose proof (all_residues_spec _ r c hj_tile_lines) as H. cbv beta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H].
  unfold hj_has_v in H. apply existsb_exists in H as [j [Hj Ht]].
  apply in_seq in Hj. apply Nat.eqb_eq in Ht.
  exists j. split; [lia |]. unfold hj_kind. rewrite (mod8_add r j). exact Ht.
Qed.

Lemma hj_window_d : forall r c, exists j, j < 8 /\ hj_kind (r + j) (c + j) = 4.
Proof.
  intros r c. pose proof (all_residues_spec _ r c hj_tile_lines) as H. cbv beta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  unfold hj_has_d in H. apply existsb_exists in H as [j [Hj Ht]].
  apply in_seq in Hj. apply Nat.eqb_eq in Ht.
  exists j. split; [lia |]. unfold hj_kind. rewrite (mod8_add r j), (mod8_add c j). exact Ht.
Qed.

Lemma hj_window_a : forall r s, 8 <= s -> exists t, t < 8 /\ hj_kind (r + t) (s - t) = 6.
Proof.
  intros r s Hs. pose proof (all_residues_spec _ r s hj_tile_lines) as H. cbv beta in H.
  apply andb_true_iff in H as [_ H].
  unfold hj_has_a in H. apply existsb_exists in H as [t [Ht Htile]].
  apply in_seq in Ht. apply Nat.eqb_eq in Htile.
  exists t. split; [lia |]. unfold hj_kind.
  rewrite (mod8_add r t), (mod8_sub s t) by lia. exact Htile.
Qed.

Theorem hj_line_has_pair : forall m n k L, 9 <= k -> In L (gen_lines m n k) ->
  exists x, In x L /\ In (hj_partner m n x) L /\ hj_partner m n x <> x.
Proof.
  intros m n k L Hk HL. apply in_gen_lines in HL as (d & r & c & Hfit & ->).
  destruct d; simpl in Hfit.
  - (* horizontal: cells (r, c + i) *)
    destruct (hj_window_h r c) as [j [Hj Hkind]].
    exists (r * n + (c + j)).
    rewrite hj_partner_rc by lia. unfold hj_step. rewrite Hkind. cbv beta iota.
    destruct (Nat.ltb_spec (c + j + 1) n) as [_ | Hbad]; [| lia].
    split; [| split].
    + apply in_mkline. exists j. split; [lia | reflexivity].
    + apply in_mkline. exists (j + 1). split; [lia |]. cbn [fst snd cell_at].
      replace (c + (j + 1)) with (c + j + 1) by lia. reflexivity.
    + lia.
  - (* vertical: cells (r + i, c) *)
    destruct (hj_window_v r c) as [j [Hj Hkind]].
    exists ((r + j) * n + c).
    rewrite hj_partner_rc by lia. unfold hj_step. rewrite Hkind. cbv beta iota.
    destruct (Nat.ltb_spec (r + j + 1) m) as [_ | Hbad]; [| lia].
    split; [| split].
    + apply in_mkline. exists j. split; [lia | reflexivity].
    + apply in_mkline. exists (j + 1). split; [lia |]. cbn [fst snd cell_at].
      replace (r + (j + 1)) with (r + j + 1) by lia. reflexivity.
    + nia.
  - (* diagonal: cells (r + i, c + i) *)
    destruct (hj_window_d r c) as [j [Hj Hkind]].
    exists ((r + j) * n + (c + j)).
    rewrite hj_partner_rc by lia. unfold hj_step. rewrite Hkind. cbv beta iota.
    destruct (Nat.ltb_spec (r + j + 1) m) as [_ | Hbad]; [| lia].
    destruct (Nat.ltb_spec (c + j + 1) n) as [_ | Hbad]; [| lia].
    cbn [andb].
    split; [| split].
    + apply in_mkline. exists j. split; [lia | reflexivity].
    + apply in_mkline. exists (j + 1). split; [lia |]. cbn [fst snd cell_at].
      replace (r + (j + 1)) with (r + j + 1) by lia.
      replace (c + (j + 1)) with (c + j + 1) by lia. reflexivity.
    + nia.
  - (* anti-diagonal: cells (r + (k - 1 - i), c + i), walked from the top *)
    assert (Hs : 8 <= c + k - 1) by lia.
    destruct (hj_window_a r (c + k - 1) Hs) as [t [Ht Hkind]].
    exists ((r + t) * n + (c + k - 1 - t)).
    rewrite hj_partner_rc by lia. unfold hj_step. rewrite Hkind. cbv beta iota.
    destruct (Nat.ltb_spec (r + t + 1) m) as [_ | Hbad]; [| lia].
    destruct (Nat.leb_spec 1 (c + k - 1 - t)) as [_ | Hbad]; [| lia].
    cbn [andb].
    split; [| split].
    + apply in_mkline. exists (k - 1 - t). split; [lia |]. cbn [fst snd cell_at].
      replace (r + (k - 1 - (k - 1 - t))) with (r + t) by lia.
      replace (c + (k - 1 - t)) with (c + k - 1 - t) by lia. reflexivity.
    + apply in_mkline. exists (k - 2 - t). split; [lia |]. cbn [fst snd cell_at].
      replace (r + (k - 1 - (k - 2 - t))) with (r + t + 1) by lia.
      replace (c + (k - 2 - t)) with (c + k - 1 - t - 1) by lia. reflexivity.
    + nia.
Qed.

(* ========================================================================= *)
(** * 6. The theorems                                                        *)
(* ========================================================================= *)

(** Maker-Breaker: with lines of 9 or more, Breaker wins on every board,
    whoever moves first. *)
Theorem mnk_hales_jewett_breaker_wins : forall m n k p d, 9 <= k ->
  ~ maker_wins (gen_lines m n k) p d (empty_board (m * n)).
Proof.
  intros m n k p d Hk.
  apply (pairing_no_maker_win_empty (gen_lines m n k) (hj_partner m n) (m * n)).
  - apply hj_partner_invol.
  - apply hj_partner_range.
  - intros L HL. exact (hj_line_has_pair m n k L Hk HL).
Qed.

(** Hales-Jewett: every (m, n, k) game with k >= 9 is a draw. *)
Theorem mnk_hales_jewett_draw : forall m n k, 9 <= k ->
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof.
  intros m n k Hk.
  apply (pairing_draw (gen_lines m n k) (hj_partner m n) (m * n)).
  - apply hj_partner_invol.
  - apply hj_partner_range.
  - intros L HL. exact (hj_line_has_pair m n k L Hk HL).
Qed.
