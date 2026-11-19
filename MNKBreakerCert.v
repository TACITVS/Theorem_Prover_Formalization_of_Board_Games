(** * MNKBreakerCert.v: A Sound Checker for Breaker Strategies

    A Breaker strategy certifies that Maker cannot win: within a given number
    of Maker moves (a speed lower bound), or ever (a Maker-Breaker Breaker win,
    hence a draw of the strong game by [breaker_win_draw]).

    - [brcert]: a strategy tree for Breaker.  At a node, Maker is to move; the
      node lists, for every Maker move that leaves Breaker a reply, one
      Breaker reply and the rest of the strategy.  A leaf is a position the
      checker settles by computation:
        [BrES]     the Erdos-Selfridge criterion ([erdos_selfridge_potential]);
        [BrPair]   a pairing of free cells meeting every open line
                   ([pairing_no_maker_win]);
        [BrShort]  every open line lacks more Maker stones than Maker has
                   moves left ([short_no_win]; bounded certificates only).
    - [check_br lines p ob b ct]: decidable checker.  [ob = Some d] bounds
      Maker to [d] more moves; [ob = None] is unbounded.
    - [check_br_sound]: an accepted certificate proves [~ maker_wins].
    - [mnk_no_win_before_k]: with no certificate at all, nobody completes k in
      a row from the empty board in fewer than k own moves, in the
      Maker-Breaker game and in the strong game.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From MNK Require Import MNKBoard MNKGame MNKErdosSelfridge MNKMakerBreaker.

(* ========================================================================= *)
(** * 1. Certificates                                                        *)
(* ========================================================================= *)

Inductive brcert : Type :=
  | BrES    : brcert
  | BrPair  : list (nat * nat) -> brcert
  | BrShort : brcert
  | BrNode  : brmoves -> brcert
with brmoves : Type :=
  | BmNil  : brmoves
  | BmCons : nat -> nat -> brcert -> brmoves -> brmoves.  (* Maker move, Breaker reply *)

Scheme brcert_mut := Induction for brcert Sort Prop
  with brmoves_mut := Induction for brmoves Sort Prop.

Fixpoint has_move (m : nat) (ms : brmoves) : bool :=
  match ms with
  | BmNil => false
  | BmCons m' _ _ rest => (m =? m') || has_move m rest
  end.

Fixpoint InM (m c : nat) (sub : brcert) (ms : brmoves) : Prop :=
  match ms with
  | BmNil => False
  | BmCons m' c' s rest => (m = m' /\ c = c' /\ sub = s) \/ InM m c sub rest
  end.

Lemma has_move_InM : forall m ms, has_move m ms = true -> exists c sub, InM m c sub ms.
Proof.
  intros m ms. induction ms as [| m' c' s rest IH]; simpl; [discriminate |].
  intros H. apply orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. subst. exists c', s. left. auto.
  - destruct (IH H) as [c [sub Hs]]. exists c, sub. right. exact Hs.
Qed.

(** Number of positions in a certificate: its nodes and leaves. *)
Fixpoint brcert_size (ct : brcert) : nat :=
  match ct with
  | BrNode ms => S (brmoves_size ms)
  | _ => 1
  end
with brmoves_size (ms : brmoves) : nat :=
  match ms with
  | BmNil => 0
  | BmCons _ _ sub rest => brcert_size sub + brmoves_size rest
  end.

(** The partner function of a list of pairs; unpaired cells are their own
    partners.  The checker verifies whatever it needs about it. *)
Fixpoint pair_lookup (ps : list (nat * nat)) (x : nat) : nat :=
  match ps with
  | [] => x
  | (a, c) :: rest => if x =? a then c else if x =? c then a else pair_lookup rest x
  end.

(** The move bound: [None] is unbounded, [Some d] allows [d] Maker moves. *)
Definition within (ob : option nat) (d : nat) : Prop :=
  match ob with
  | None => True
  | Some d0 => d <= d0
  end.

(* ========================================================================= *)
(** * 2. Board helpers                                                       *)
(* ========================================================================= *)

Lemma filter_drop_one_le : forall (f : nat -> bool) m L, NoDup L ->
  length (filter f L) <= S (length (filter (fun x => f x && negb (x =? m)) L)).
Proof.
  intros f m L. induction L as [| a L IH]; intros Hnd; simpl; [lia |].
  inversion Hnd as [| a' L' Hna HndL]; subst.
  specialize (IH HndL).
  destruct (Nat.eqb_spec a m) as [-> | Ham].
  - assert (E : filter (fun x => f x && negb (x =? m)) L = filter f L).
    { apply filter_ext_in. intros x Hx.
      destruct (Nat.eqb_spec x m) as [-> | _]; [contradiction |].
      rewrite andb_true_r. reflexivity. }
    rewrite andb_false_r, E. destruct (f m); simpl; lia.
  - rewrite andb_true_r. destruct (f a); simpl; lia.
Qed.

Lemma filter_all_false : forall (f : nat -> bool) L,
  (forall x, In x L -> f x = false) -> filter f L = [].
Proof.
  intros f L. induction L as [| a L IH]; intros H; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma get_cell_some_lt : forall b x q, get_cell b x = Some q -> x < length b.
Proof.
  intros b x q H. unfold get_cell in H.
  destruct (Nat.lt_ge_cases x (length b)) as [Hlt | Hge]; [exact Hlt |].
  rewrite nth_overflow in H by exact Hge. discriminate.
Qed.

(** A stone stays where it is when another (legal) move is played. *)
Lemma owned_stays : forall b x r q y,
  is_legal_move b x = true -> cell_owned_by b q y = true ->
  cell_owned_by (set_cell b x r) q y = true.
Proof.
  intros b x r q y Hx Hy. apply cell_owned_iff in Hy. apply cell_owned_iff.
  assert (Hxy : x <> y) by (intros ->; apply legal_move_empty in Hx; congruence).
  rewrite get_set_cell_other by exact Hxy. exact Hy.
Qed.

Lemma maker_wins_inv : forall lines p d b, maker_wins lines p d b ->
  exists d' m, d = S d' /\ is_legal_move b m = true /\
    (check_win (set_cell b m p) p lines = true \/
     ((exists c, is_legal_move (set_cell b m p) c = true) /\
      forall c, is_legal_move (set_cell b m p) c = true ->
        maker_wins lines p d' (set_cell (set_cell b m p) c (other_player p)))).
Proof.
  intros lines p d b H. destruct H as [d b m Hm Hw | d b m Hm Hex Hnext].
  - exists d, m. auto.
  - exists d, m. auto.
Qed.

(* ========================================================================= *)
(** * 3. Leaf rules and the checker                                          *)
(* ========================================================================= *)

Section Checker.

Variable lines : list (list nat).
Variable p : player.
Hypothesis lines_nodup : forall L, In L lines -> NoDup L.

(** Breaker has a stone on [L]. *)
Definition blocked (b : board_t) (L : list nat) : bool :=
  existsb (cell_owned_by b (other_player p)) L.

(** Cells of [L] Maker still has to claim. *)
Definition missing (b : board_t) (L : list nat) : nat :=
  length (filter (fun x => negb (cell_owned_by b p x)) L).

Lemma blocked_stays : forall b x r L,
  is_legal_move b x = true -> blocked b L = true -> blocked (set_cell b x r) L = true.
Proof.
  intros b x r L Hx H. unfold blocked in *. apply existsb_exists in H as [y [Hy Hby]].
  apply existsb_exists. exists y. split; [exact Hy |]. apply owned_stays; assumption.
Qed.

(** A Maker move fills at most one missing cell of a line ... *)
Lemma missing_maker_move : forall b m L, NoDup L -> is_legal_move b m = true ->
  missing b L <= S (missing (set_cell b m p) L).
Proof.
  intros b m L Hnd Hm. unfold missing.
  rewrite (filter_ext_in (fun x => negb (cell_owned_by (set_cell b m p) p x))
                         (fun x => negb (cell_owned_by b p x) && negb (x =? m))).
  - apply filter_drop_one_le. exact Hnd.
  - intros x _. destruct (Nat.eqb_spec x m) as [-> | Hxm].
    + unfold cell_owned_by. rewrite get_set_cell_same by (apply legal_move_lt; exact Hm).
      rewrite player_eqb_refl, andb_false_r. reflexivity.
    + unfold cell_owned_by. rewrite get_set_cell_other by congruence.
      rewrite andb_true_r. reflexivity.
Qed.

(** ... and a Breaker move fills none. *)
Lemma missing_breaker_move : forall b c L, is_legal_move b c = true ->
  missing (set_cell b c (other_player p)) L = missing b L.
Proof.
  intros b c L Hc. unfold missing. f_equal. apply filter_ext. intros x.
  unfold cell_owned_by. destruct (Nat.eqb_spec x c) as [-> | Hxc].
  - rewrite get_set_cell_same by (apply legal_move_lt; exact Hc).
    rewrite (legal_move_empty b c Hc). destruct p; reflexivity.
  - rewrite get_set_cell_other by congruence. reflexivity.
Qed.

(** If every line is blocked or lacks more than [d] Maker stones, Maker
    cannot complete a line within [d] moves. *)
Theorem short_no_win : forall d b,
  (forall L, In L lines -> blocked b L = true \/ d < missing b L) ->
  ~ maker_wins lines p d b.
Proof.
  intros d b Hs H. revert Hs.
  induction H as [d b m Hm Hw | d b m Hm Hex Hnext IH]; intros Hs.
  - apply check_win_iff in Hw as [L [HL Hown]].
    destruct (Hs L HL) as [Hbl | Hlt].
    + unfold blocked in Hbl. apply existsb_exists in Hbl as [y [Hy Hby]].
      apply cell_owned_iff in Hby. pose proof (Hown y Hy) as Oy.
      assert (Hym : m <> y) by (intros ->; apply legal_move_empty in Hm; congruence).
      rewrite get_set_cell_other in Oy by exact Hym.
      rewrite Hby in Oy. inversion Oy as [Hop]. exact (mb_other_neq p Hop).
    + assert (H0 : missing (set_cell b m p) L = 0).
      { unfold missing. rewrite filter_all_false; [reflexivity |].
        intros x Hx. apply negb_false_iff. apply cell_owned_iff. exact (Hown x Hx). }
      pose proof (missing_maker_move b m L (lines_nodup L HL) Hm) as Hle. lia.
  - destruct Hex as [c Hc]. apply (IH c Hc). intros L HL.
    destruct (Hs L HL) as [Hbl | Hlt]; [left | right].
    + apply blocked_stays; [exact Hc |]. apply blocked_stays; assumption.
    + rewrite missing_breaker_move by exact Hc.
      pose proof (missing_maker_move b m L (lines_nodup L HL) Hm) as Hle. lia.
Qed.

Definition short_ok (d : nat) (b : board_t) : bool :=
  forallb (fun L => blocked b L || (d <? missing b L)) lines.

Lemma short_ok_sound : forall d0 b, short_ok d0 b = true ->
  forall d, d <= d0 -> ~ maker_wins lines p d b.
Proof.
  intros d0 b H d Hd. apply short_no_win. intros L HL.
  unfold short_ok in H. rewrite forallb_forall in H.
  pose proof (H L HL) as HLine.
  apply orb_true_iff in HLine as [Hb | Hlt]; [left; exact Hb | right].
  apply Nat.ltb_lt in Hlt. lia.
Qed.

(** Erdos-Selfridge with K the longest line length. *)
Definition es_bound : nat := list_max (map (@length nat) lines).

Definition es_ok (b : board_t) : bool :=
  forallb (fun x => phi es_bound b p lines + wgt es_bound b p lines x <? 2 ^ es_bound)
          (legal_moves b).

Lemma es_ok_sound : forall d b, es_ok b = true -> ~ maker_wins lines p d b.
Proof.
  intros d b H. apply (erdos_selfridge_potential lines es_bound).
  - intros L HL. split; [exact (lines_nodup L HL) |].
    assert (Hall : Forall (fun k => k <= es_bound) (map (@length nat) lines))
      by (apply list_max_le; unfold es_bound; lia).
    rewrite Forall_forall in Hall. apply Hall. apply in_map. exact HL.
  - intros x Hx. unfold es_ok in H. rewrite forallb_forall in H.
    apply Nat.ltb_lt. apply H. apply in_legal_moves. exact Hx.
Qed.

(** Pairing: [ps] is an involution on the cells, every paired Maker stone has
    a Breaker partner, and every line is blocked or contains a whole pair. *)
Definition pairing_ok (b : board_t) (ps : list (nat * nat)) : bool :=
  let f := pair_lookup ps in
  forallb (fun x => (f (f x) =? x) && (f x <? length b)) (seq 0 (length b)) &&
  forallb (fun x => negb (cell_owned_by b p x) || (f x =? x) ||
                    cell_owned_by b (other_player p) (f x)) (seq 0 (length b)) &&
  forallb (fun L => blocked b L ||
                    existsb (fun x => negb (f x =? x) && existsb (Nat.eqb (f x)) L) L) lines.

Lemma pairing_ok_sound : forall d b ps, pairing_ok b ps = true -> ~ maker_wins lines p d b.
Proof.
  intros d b ps H. unfold pairing_ok in H.
  apply andb_true_iff in H as [H Hlines]. apply andb_true_iff in H as [Hinv Hans].
  rewrite forallb_forall in Hinv, Hans, Hlines.
  set (f := pair_lookup ps) in *.
  assert (Hcell : forall x, x < length b ->
            f (f x) = x /\ f x < length b).
  { intros x Hx. assert (Hin : In x (seq 0 (length b))) by (apply in_seq; lia).
    specialize (Hinv x Hin). apply andb_true_iff in Hinv as [H1 H2].
    split; [apply Nat.eqb_eq; exact H1 | apply Nat.ltb_lt; exact H2]. }
  apply (pairing_no_maker_win lines f (length b)
           (fun x Hx => proj1 (Hcell x Hx)) (fun x Hx => proj2 (Hcell x Hx)) p d b).
  - split; [reflexivity |]. intros x Ox Hneq.
    assert (Hin : In x (seq 0 (length b))) by (apply in_seq; apply get_cell_some_lt in Ox; lia).
    specialize (Hans x Hin).
    apply orb_true_iff in Hans as [Hans | Hb].
    + apply orb_true_iff in Hans as [Hn | Hfx].
      * apply negb_true_iff in Hn. apply cell_owned_iff in Ox. congruence.
      * apply Nat.eqb_eq in Hfx. contradiction.
    + apply cell_owned_iff. exact Hb.
  - intros L HL. specialize (Hlines L HL). apply orb_true_iff in Hlines as [Hb | He].
    + left. unfold blocked in Hb. apply existsb_exists in Hb as [y [Hy Hby]].
      exists y. split; [exact Hy | apply cell_owned_iff; exact Hby].
    + right. apply existsb_exists in He as [x [Hx Hxe]].
      apply andb_true_iff in Hxe as [Hne Hin].
      apply existsb_exists in Hin as [y [Hy Hfy]]. apply Nat.eqb_eq in Hfy.
      exists x. split; [exact Hx |]. split; [rewrite Hfy; exact Hy |].
      apply negb_true_iff in Hne. apply Nat.eqb_neq in Hne. exact Hne.
Qed.

Fixpoint check_br (ob : option nat) (b : board_t) (ct : brcert) {struct ct} : bool :=
  match ct with
  | BrES => es_ok b
  | BrPair ps => pairing_ok b ps
  | BrShort =>
      match ob with
      | Some d => short_ok d b
      | None => false
      end
  | BrNode ms =>
      forallb (fun m => let b1 := set_cell b m p in
                        negb (check_win b1 p lines) &&
                        (negb (nonempty (legal_moves b1)) || has_move m ms))
              (legal_moves b) &&
      check_moves (option_map pred ob) b ms
  end
with check_moves (ob : option nat) (b : board_t) (ms : brmoves) {struct ms} : bool :=
  match ms with
  | BmNil => true
  | BmCons m c sub rest =>
      let b1 := set_cell b m p in
      is_legal_move b1 c && check_br ob (set_cell b1 c (other_player p)) sub &&
      check_moves ob b rest
  end.

Lemma check_moves_spec : forall ms ob b,
  check_moves ob b ms = true ->
  forall m c sub, InM m c sub ms ->
    is_legal_move (set_cell b m p) c = true /\
    check_br ob (set_cell (set_cell b m p) c (other_player p)) sub = true.
Proof.
  induction ms as [| m' c' s rest IH]; intros ob b H m c sub Hin; simpl in *; [contradiction |].
  apply andb_true_iff in H as [H Hrest]. apply andb_true_iff in H as [Hc Hs].
  destruct Hin as [[-> [-> ->]] | Hin].
  - split; assumption.
  - eapply IH; eauto.
Qed.

(** Soundness: an accepted certificate is a Breaker strategy that stops
    Maker for as many moves as the bound allows. *)
Theorem check_br_sound : forall ct ob b, check_br ob b ct = true ->
  forall d, within ob d -> ~ maker_wins lines p d b.
Proof.
  apply (brcert_mut
    (fun ct => forall ob b, check_br ob b ct = true ->
       forall d, within ob d -> ~ maker_wins lines p d b)
    (fun ms => forall m c sub, InM m c sub ms ->
       forall ob b, check_br ob b sub = true ->
       forall d, within ob d -> ~ maker_wins lines p d b)).
  - (* Erdos-Selfridge leaf *)
    intros ob b H d _. exact (es_ok_sound d b H).
  - (* pairing leaf *)
    intros ps ob b H d _. exact (pairing_ok_sound d b ps H).
  - (* too few Maker moves left *)
    intros [d0 |] b H d Hd; simpl in H; [| discriminate].
    exact (short_ok_sound d0 b H d Hd).
  - (* a Maker-to-move node *)
    intros ms IHms ob b H d Hd Hw. simpl in H.
    apply andb_true_iff in H as [Hall Hms]. rewrite forallb_forall in Hall.
    destruct (maker_wins_inv lines p d b Hw) as (d' & m & -> & Hm & [Hwin | [Hex Hnext]]).
    + specialize (Hall m (proj2 (in_legal_moves b m) Hm)).
      apply andb_true_iff in Hall as [Hnw _]. rewrite Hwin in Hnw. discriminate.
    + specialize (Hall m (proj2 (in_legal_moves b m) Hm)).
      apply andb_true_iff in Hall as [_ Hcov]. apply orb_true_iff in Hcov as [Hfull | Hhas].
      * destruct Hex as [c Hc].
        assert (Hne : nonempty (legal_moves (set_cell b m p)) = true)
          by (apply nonempty_iff; exists c; apply in_legal_moves; exact Hc).
        rewrite Hne in Hfull. discriminate.
      * destruct (has_move_InM m ms Hhas) as [c [sub Hin]].
        destruct (check_moves_spec ms _ b Hms m c sub Hin) as [Hc Hsub].
        apply (IHms m c sub Hin _ _ Hsub d').
        -- destruct ob as [d0 |]; simpl in *; [lia | exact I].
        -- exact (Hnext c Hc).
  - (* BmNil *)
    intros m c sub [].
  - (* BmCons *)
    intros m c s Hs rest Hrest m' c' sub Hin.
    destruct Hin as [[-> [-> ->]] | Hin].
    + exact Hs.
    + exact (Hrest m' c' sub Hin).
Qed.

Corollary check_br_draw : forall ct b,
  check_br None b ct = true -> forall d, ~ maker_wins lines p d b.
Proof. intros ct b H d. exact (check_br_sound ct None b H d I). Qed.

Corollary check_br_within : forall ct d b,
  check_br (Some d) b ct = true -> ~ maker_wins lines p d b.
Proof. intros ct d b H. exact (check_br_sound ct (Some d) b H d (le_n d)). Qed.

End Checker.

(* ========================================================================= *)
(** * 4. No k in a row in fewer than k moves                                 *)
(* ========================================================================= *)

(** From the empty board, every line still lacks all k of its cells. *)
Theorem mnk_no_win_before_k : forall m n k p d, d < k ->
  ~ maker_wins (gen_lines m n k) p d (empty_board (m * n)).
Proof.
  intros m n k p d Hd. apply short_no_win.
  - intros L HL. eapply gen_lines_nodup. exact HL.
  - intros L HL. right. unfold missing.
    rewrite (filter_ext_in _ (fun _ => true)).
    + rewrite filter_true. rewrite (gen_lines_uniform m n k L HL). exact Hd.
    + intros x _. unfold cell_owned_by. rewrite get_cell_empty_board. reflexivity.
Qed.

Corollary mnk_no_forced_win_before_k : forall m n k p d, d < k ->
  ~ forces_win (gen_lines m n k) p d (empty_board (m * n)).
Proof.
  intros m n k p d Hd Hw. apply (mnk_no_win_before_k m n k p d Hd).
  apply forces_win_maker_wins. exact Hw.
Qed.
