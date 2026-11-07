(** * Connect-5 (8x8): Strategy Certificate and Game Value Equivalence

    This file connects:
    1. Inductive strategy trees ([strategy d b s]) combining explicit
       game-tree search with follow-up pairing structures ([Static d b st]).
    2. The inductive game semantics ([safe d b s]).
    3. The minimax value ([game_value = value 64 initial White]).

    Main results:
    - [strategy_sound]: any strategy tree proves [safe d b s].
    - [mutual_safety_draw]: if Black is safe from the initial board, and
      White is safe after an opening move [c0], then [game_value = Draw].
    - [connect5_8x8_fair]: if both players have strategy certificates,
      then the variant (8, 8, 5) is provably a fair game (draw).
*)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

From C5 Require Import C5Game C5Board C5Principle C5Rules.

(** ** Strategy tree datatype *)

Inductive strategy (d : player) : board -> player -> Prop :=
| StratFull : forall b s,
    full b = true -> strategy d b s
| StratLeaf : forall b st,
    Static d b st -> strategy d b (other d)
| StratDefWin : forall b c,
    legal b c = true ->
    has_line (play b c d) d = true ->
    strategy d b d
| StratDef : forall b c,
    legal b c = true ->
    strategy d (play b c d) (other d) ->
    strategy d b d
| StratAtt : forall b,
    full b = false ->
    (forall c, legal b c = true ->
       has_line (play b c (other d)) (other d) = false /\
       strategy d (play b c (other d)) d) ->
    strategy d b (other d).

(** ** Soundness of strategy trees *)

Fixpoint strategy_sound (d : player) (b : board) (s : player)
                        (strat : strategy d b s) : safe d b s :=
  match strat with
  | StratFull _ _ _ Hfull =>
      safe_full d _ _ Hfull
  | StratLeaf _ _ st Hst =>
      structure_sound d _ st Hst
  | StratDefWin _ _ c Hleg Hwin =>
      safe_def d _ c Hleg (or_introl Hwin)
  | StratDef _ _ c Hleg srec =>
      safe_def d _ c Hleg (or_intror (strategy_sound d _ _ srec))
  | StratAtt _ _ Hfull Hbranches =>
      safe_att d _ Hfull
        (fun c Hc =>
           let '(conj Hnl srec) := Hbranches c Hc in
           conj Hnl (strategy_sound d _ _ srec))
  end.

(** ** Algebraic properties of minimax results *)

Lemma rmax_Loss_r : forall r, rmax Loss r = r.
Proof. destruct r; reflexivity. Qed.

Lemma rmax_r_Loss : forall r, rmax r Loss = r.
Proof. destruct r; reflexivity. Qed.

Lemma rmax_Win_r : forall r, rmax Win r = Win.
Proof. destruct r; reflexivity. Qed.

Lemma rmax_r_Win : forall r, rmax r Win = Win.
Proof. destruct r; reflexivity. Qed.

Lemma rmax_eq_Win : forall r1 r2, rmax r1 r2 = Win <-> r1 = Win \/ r2 = Win.
Proof.
  intros r1 r2. destruct r1, r2; simpl; split; intros; auto; try discriminate;
  destruct H; discriminate.
Qed.

Lemma rmax_eq_Loss : forall r1 r2, rmax r1 r2 = Loss <-> r1 = Loss /\ r2 = Loss.
Proof.
  intros r1 r2. destruct r1, r2; simpl; split; intros; auto; try discriminate;
  destruct H; discriminate.
Qed.

Lemma neg_eq_Win : forall r, neg r = Win <-> r = Loss.
Proof. destruct r; simpl; split; intros; auto; discriminate. Qed.

Lemma neg_eq_Loss : forall r, neg r = Loss <-> r = Win.
Proof. destruct r; simpl; split; intros; auto; discriminate. Qed.

Lemma neg_neq_Win : forall r, neg r <> Win <-> r <> Loss.
Proof. destruct r; simpl; split; intros; discriminate || contradiction || auto. Qed.

Lemma neg_neq_Loss : forall r, neg r <> Loss <-> r <> Win.
Proof. destruct r; simpl; split; intros; discriminate || contradiction || auto. Qed.

Definition step_val (f : nat) (b : board) (s : player) (c : nat) : result :=
  if has_line (play b c s) s then Win
  else neg (value f (play b c s) (other s)).

Definition fold_step (f : nat) (b : board) (s : player) (acc : result) (c : nat) : result :=
  if legal b c then rmax acc (step_val f b s c) else acc.

Lemma value_S_fold : forall f b s,
  full b = false ->
  value (S f) b s = fold_left (fold_step f b s) (seq 0 8) Loss.
Proof.
  intros f b s Hfull. simpl. rewrite Hfull. reflexivity.
Qed.

Lemma fold_step_Win : forall f b s l acc,
  fold_left (fold_step f b s) l acc = Win <->
  acc = Win \/ exists c, In c l /\ legal b c = true /\ step_val f b s c = Win.
Proof.
  intros f b s l.
  induction l as [|c0 l' IH]; intros acc; simpl.
  - split.
    + intros ->; left; reflexivity.
    + intros [->|[c [Hin _]]]; [reflexivity|destruct Hin].
  - rewrite IH. unfold fold_step.
    destruct (legal b c0) eqn:Eleg.
    + rewrite rmax_eq_Win. split.
      * intros [[->|Hstep]|[c [Hin [Hl Hs]]]].
        -- left; reflexivity.
        -- right; exists c0; split; [left; reflexivity|split; assumption].
        -- right; exists c; split; [right; assumption|split; assumption].
      * intros [->|[c [[<-|Hin] [Hl Hs]]]].
        -- left; left; reflexivity.
        -- left; right; exact Hs.
        -- right; exists c; split; [assumption|split; assumption].
    + split.
      * intros [Hacc|[c [Hin [Hl Hs]]]].
        -- left; exact Hacc.
        -- right; exists c; split; [right; exact Hin|split; assumption].
      * intros [Hacc|[c [[<-|Hin] [Hl Hs]]]].
        -- left; exact Hacc.
        -- congruence.
        -- right; exists c; split; [exact Hin|split; assumption].
Qed.

Lemma fold_step_not_Win : forall f b s l,
  (forall c, In c l -> legal b c = true -> step_val f b s c <> Win) ->
  fold_left (fold_step f b s) l Loss <> Win.
Proof.
  intros f b s l Hstep.
  rewrite fold_step_Win.
  intros [Hloss | [c [Hin [Hleg Hwin]]]].
  - discriminate Hloss.
  - apply (Hstep c Hin Hleg); exact Hwin.
Qed.

Lemma fold_step_Loss : forall f b s l acc,
  fold_left (fold_step f b s) l acc = Loss <->
  acc = Loss /\ (forall c, In c l -> legal b c = true -> step_val f b s c = Loss).
Proof.
  intros f b s l.
  induction l as [|c0 l' IH]; intros acc; simpl.
  - split.
    + intros ->; split; [reflexivity|intros c Hin; destruct Hin].
    + intros [-> _]; reflexivity.
  - rewrite IH. unfold fold_step.
    destruct (legal b c0) eqn:Eleg.
    + rewrite rmax_eq_Loss. split.
      * intros [[Hacc Hstep] Hall]. split; [exact Hacc|].
        intros c [<-|Hin] Hl; [exact Hstep | apply (Hall c Hin Hl)].
      * intros [Hacc Hall]. split.
        -- split; [exact Hacc | apply (Hall c0 (or_introl eq_refl) Eleg)].
        -- intros c Hin Hl; apply (Hall c (or_intror Hin) Hl).
    + split.
      * intros [Hacc Hall]. split; [exact Hacc|].
        intros c [<-|Hin] Hl; [congruence | apply (Hall c Hin Hl)].
      * intros [Hacc Hall]. split; [exact Hacc|].
        intros c Hin Hl; apply (Hall c (or_intror Hin) Hl).
Qed.

Lemma fold_step_not_Loss : forall f b s l c0,
  In c0 l ->
  legal b c0 = true ->
  step_val f b s c0 <> Loss ->
  fold_left (fold_step f b s) l Loss <> Loss.
Proof.
  intros f b s l c0 Hin Hleg Hnot.
  rewrite fold_step_Loss.
  intros [_ Hall].
  apply Hnot. apply (Hall c0 Hin Hleg).
Qed.

(** ** Connecting game semantics to minimax value *)

Theorem safe_defense_sound : forall fuel,
  (forall b d, safe d b (other d) -> value fuel b (other d) <> Win) /\
  (forall b d, safe d b d -> value fuel b d <> Loss).
Proof.
  induction fuel as [|f [IH_att IH_def]].
  - split; intros b d Hsafe; simpl; discriminate.
  - split.
    + intros b d Hsafe.
      destruct (full b) eqn:Efull.
      * simpl; rewrite Efull; discriminate.
      * rewrite value_S_fold by exact Efull.
        apply fold_step_not_Win.
        intros c Hin Hleg.
        inversion Hsafe as [b0 s0 Efull'
                           |b0 c0 Hleg0 Hdef0
                           |b0 Efull0 Hcases]; subst.
        -- rewrite Efull in Efull'; discriminate.
        -- destruct d; discriminate.
        -- destruct (Hcases c Hleg) as [Hnl Hsafe'].
           unfold step_val.
           rewrite Hnl.
           rewrite neg_neq_Win.
           rewrite other_other.
           apply (IH_def (play b c (other d)) d Hsafe').
    + intros b d Hsafe.
      destruct (full b) eqn:Efull.
      * simpl; rewrite Efull; discriminate.
      * rewrite value_S_fold by exact Efull.
        inversion Hsafe as [b0 s0 Efull'
                           |b0 c0 Hleg0 Hdef0
                           |b0 Efull0 Hcases]; subst.
        -- rewrite Efull in Efull'; discriminate.
        -- assert (Hin0 : In c0 (seq 0 8)).
           { apply legal_spec in Hleg0 as [Hc8 _].
             apply in_seq; simpl; lia. }
           apply (fold_step_not_Loss f b d (seq 0 8) c0 Hin0 Hleg0).
           unfold step_val.
           destruct Hdef0 as [Hwin | Hsafe'].
           ++ rewrite Hwin; discriminate.
           ++ destruct (has_line (play b c0 d) d) eqn:Eline.
              ** discriminate.
              ** rewrite neg_neq_Loss.
                 apply (IH_att (play b c0 d) d Hsafe').
        -- destruct d; discriminate.
Qed.

Lemma safe_att_not_win : forall fuel b d,
  safe d b (other d) -> value fuel b (other d) <> Win.
Proof.
  intros fuel b d. apply (proj1 (safe_defense_sound fuel)).
Qed.

Lemma safe_def_not_loss : forall fuel b d,
  safe d b d -> value fuel b d <> Loss.
Proof.
  intros fuel b d. apply (proj2 (safe_defense_sound fuel)).
Qed.

(** ** Mutual safety implies game is a draw *)

Lemma initial_not_full : full initial = false.
Proof.
  unfold full, initial; simpl.
  reflexivity.
Qed.

Theorem mutual_safety_draw : forall c0,
  legal initial c0 = true ->
  safe White (play initial c0 White) Black ->
  safe Black initial White ->
  game_value = Draw.
Proof.
  intros c0 Hleg sW sB.
  unfold game_value.
  assert (Hnot_win : value 64 initial White <> Win).
  { pose proof (safe_att_not_win 64 initial Black) as Hw.
    exact (Hw sB). }
  assert (Hnot_loss : value 64 initial White <> Loss).
  { rewrite value_S_fold by exact initial_not_full.
    assert (Hin0 : In c0 (seq 0 8)).
    { apply legal_spec in Hleg as [Hc8 _]. apply in_seq; simpl; lia. }
    apply (fold_step_not_Loss 63 initial White (seq 0 8) c0 Hin0 Hleg).
    unfold step_val.
    destruct (has_line (play initial c0 White) White) eqn:Eline.
    - discriminate.
    - rewrite neg_neq_Loss.
      change Black with (other White) in sW.
      exact (safe_att_not_win 63 (play initial c0 White) White sW). }
  destruct (value 64 initial White) eqn:Eval.
  - contradiction.
  - reflexivity.
  - contradiction.
Qed.

(** ** The Main Game Theorem *)

Theorem connect5_8x8_fair :
  (exists c0, legal initial c0 = true /\ strategy White (play initial c0 White) Black) ->
  strategy Black initial White ->
  game_value = Draw.
Proof.
  intros [c0 [Hleg sW]] sB.
  apply (mutual_safety_draw c0 Hleg).
  - apply strategy_sound; exact sW.
  - apply strategy_sound; exact sB.
Qed.

Theorem connect5_8x7_fair :
  (exists c0, legal initial c0 = true /\ strategy White (play initial c0 White) Black) ->
  strategy Black initial White ->
  game_value = Draw.
Proof. exact connect5_8x8_fair. Qed.

