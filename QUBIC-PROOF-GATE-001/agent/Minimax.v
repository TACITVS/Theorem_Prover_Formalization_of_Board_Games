(** Constructive finite-game search for the LOCKED Rules and Goal modules.

    This file proves the soundness of search and extracts total policies.
    It does NOT assert or evaluate the value of the empty 125-cell board.
    No theorem from Solution (including its admitted goals) is imported.

    White moves first. [owner = true] means White controls existential nodes;
    [owner = false] means Black controls them. [accept] specifies which final
    results the owner wants. All other nodes are universally quantified.
*)
From Stdlib Require Import List Arith Bool Lia.
From QubicTrusted Require Import Rules Goal.
Import ListNotations.

(** 125 is a representative of every out-of-range request. The locked rules
    replace any illegal request with their deterministic fallback. Including
    this representative avoids assuming opponent policies return legal moves. *)
Definition requests : list cell := seq 0 126.
Definition canonical_request (c : cell) : cell :=
  if c <? 125 then c else 125.

Definition effective_move (st : GameState) (c : cell) : cell :=
  if is_legal_move st c then c else next_available_cell st.

Lemma canonical_request_in : forall c, In (canonical_request c) requests.
Proof.
  intros c. unfold canonical_request, requests. apply in_seq.
  destruct (c <? 125) eqn:H; apply Nat.ltb_lt in H || apply Nat.ltb_ge in H;
    lia.
Qed.

Lemma effective_move_canonical : forall st c,
  effective_move st (canonical_request c) = effective_move st c.
Proof.
  intros st c. unfold canonical_request.
  destruct (c <? 125) eqn:H; [reflexivity|].
  unfold effective_move, is_legal_move. rewrite H. reflexivity.
Qed.

Definition move_state (turn : bool) (st : GameState) (c : cell) : GameState :=
  let d := effective_move st c in
  if turn then make_state (d :: white_stones st) (black_stones st) (d :: history st)
  else make_state (white_stones st) (d :: black_stones st) (d :: history st).

Definition move_result (turn : bool) (st : GameState) : option Result :=
  if has_win (if turn then white_stones st else black_stones st)
  then Some (if turn then WhiteWins else BlackWins)
  else if length (history st) =? 125 then Some Draw else None.

Lemma move_state_history : forall turn st c,
  length (history (move_state turn st c)) = S (length (history st)).
Proof. intros [] st c; reflexivity. Qed.

Lemma move_state_canonical : forall turn st c,
  move_state turn st (canonical_request c) = move_state turn st c.
Proof.
  intros turn st c. unfold move_state. rewrite effective_move_canonical.
  reflexivity.
Qed.

(** A one-step equation, proved by reduction against the frozen evaluator.
    A win is checked before a full-board draw; a terminal step never recurses. *)
Lemma step_game_equation : forall n turn st w b,
  step_game (S n) turn st w b =
  let st' := move_state turn st (if turn then w st else b st) in
  match move_result turn st' with
  | Some r => make_trace st' r
  | None => step_game n (negb turn) st' w b
  end.
Proof.
  intros n [] st w b; unfold move_state, move_result, effective_move;
    cbn [step_game];
    destruct (has_win _); [reflexivity| |reflexivity| ];
    destruct (length _ =? 125); reflexivity.
Qed.

Definition branch (accept : Result -> bool)
    (continuation : bool -> GameState -> bool)
    (turn : bool) (st : GameState) (c : cell) : bool :=
  let st' := move_state turn st c in
  match move_result turn st' with
  | Some r => accept r
  | None => continuation (negb turn) st'
  end.

Fixpoint solve (accept : Result -> bool) (owner : bool)
    (n : nat) (turn : bool) (st : GameState) : bool :=
  match n with
  | 0 => accept Draw
  | S rem =>
      let children := branch accept (solve accept owner rem) turn st in
      if Bool.eqb turn owner then existsb children requests
      else forallb children requests
  end.

Lemma branch_canonical : forall accept continuation turn st c,
  branch accept continuation turn st (canonical_request c) =
  branch accept continuation turn st c.
Proof.
  intros. unfold branch. rewrite move_state_canonical. reflexivity.
Qed.

(** [choose desired f] returns a request with the desired branch value,
    whenever such a request exists. The default remains a total policy. *)
Definition choose (desired : bool) (f : cell -> bool) : cell :=
  match find (fun c => Bool.eqb (f c) desired) requests with
  | Some c => c
  | None => 0
  end.

Lemma choose_spec : forall desired f,
  (exists c, In c requests /\ f c = desired) ->
  f (choose desired f) = desired.
Proof.
  intros desired f [c [Hc Hf]]. unfold choose.
  destruct (find (fun d => Bool.eqb (f d) desired) requests) eqn:Hfind.
  - apply find_some in Hfind as [_ Hfind]. apply Bool.eqb_prop in Hfind.
    exact Hfind.
  - pose proof (@find_none cell _ _ Hfind c Hc) as Hnone.
    cbn beta in Hnone.
    rewrite Hf, Bool.eqb_reflx in Hnone. discriminate.
Qed.

Lemma forallb_false_exists : forall (f : cell -> bool) l,
  forallb f l = false -> exists c, In c l /\ f c = false.
Proof.
  intros f l. induction l as [|c l IH]; cbn; intros H; [discriminate|].
  destruct (f c) eqn:Hc.
  - destruct (IH H) as [d [Hd Hfd]]. exists d. auto.
  - exists c. auto.
Qed.

(** Strategies are functions of state, as required by Rules, not functions of
    an externally supplied search horizon. The remaining horizon is recovered
    from the length of the actual history. *)
Definition search_policy (accept : Result -> bool) (owner desired : bool)
    (st : GameState) : cell :=
  choose desired
    (branch accept (solve accept owner (124 - length (history st)))
       (if desired then owner else negb owner) st).

Definition policies (owner desired : bool) (ours theirs : GameState -> cell) :=
  if Bool.eqb owner desired then (ours, theirs) else (theirs, ours).

Lemma solve_branch_selected : forall accept owner desired n turn st opponent,
  S n + length (history st) = 125 ->
  solve accept owner (S n) turn st = desired ->
  let ours := search_policy accept owner desired in
  let '(w, b) := policies owner desired ours opponent in
  branch accept (solve accept owner n) turn st (if turn then w st else b st)
    = desired.
Proof.
  intros accept owner desired n turn st opponent Hlen Hsolve.
  assert (Hdepth : 124 - length (history st) = n) by lia.
  cbn [solve] in Hsolve.
  destruct owner, desired, turn; cbn [policies Bool.eqb] in *.
  - unfold search_policy. rewrite Hdepth. apply choose_spec.
    apply existsb_exists in Hsolve. exact Hsolve.
  - apply forallb_forall with (x := canonical_request (opponent st)) in Hsolve;
      [rewrite branch_canonical in Hsolve; exact Hsolve|apply canonical_request_in].
  - destruct (branch accept (solve accept true n) true st (opponent st)) eqn:Hbranch;
      [|reflexivity].
    assert (Hin := canonical_request_in (opponent st)).
    assert (Htrue : existsb (branch accept (solve accept true n) true st) requests = true).
    { apply existsb_exists. exists (canonical_request (opponent st)).
      split; [exact Hin|rewrite branch_canonical; exact Hbranch]. }
    congruence.
  - unfold search_policy. rewrite Hdepth. apply choose_spec.
    apply forallb_false_exists in Hsolve. exact Hsolve.
  - apply forallb_forall with (x := canonical_request (opponent st)) in Hsolve;
      [rewrite branch_canonical in Hsolve; exact Hsolve|apply canonical_request_in].
  - unfold search_policy. rewrite Hdepth. apply choose_spec.
    apply existsb_exists in Hsolve. exact Hsolve.
  - unfold search_policy. rewrite Hdepth. apply choose_spec.
    apply forallb_false_exists in Hsolve. exact Hsolve.
  - destruct (branch accept (solve accept false n) false st (opponent st)) eqn:Hbranch;
      [|reflexivity].
    assert (Htrue : existsb (branch accept (solve accept false n) false st) requests = true).
    { apply existsb_exists. exists (canonical_request (opponent st)).
      split; [apply canonical_request_in|rewrite branch_canonical; exact Hbranch]. }
    congruence.
Qed.

(** Both successful and failed searches yield one fixed policy that works
    against EVERY opposing policy. No swapping of strategy quantifiers. *)
Theorem solve_policy_sound : forall accept owner desired n turn st opponent,
  n + length (history st) = 125 ->
  solve accept owner n turn st = desired ->
  let ours := search_policy accept owner desired in
  let '(w, b) := policies owner desired ours opponent in
  accept (outcome (step_game n turn st w b)) = desired.
Proof.
  intros accept owner desired n. induction n as [|n IH];
    intros turn st opponent Hlen Hsolve.
  - destruct owner, desired; exact Hsolve.
  - pose proof (solve_branch_selected accept owner desired n turn st opponent
      Hlen Hsolve) as Hbranch.
    cbv zeta in *.
    destruct (policies owner desired (search_policy accept owner desired) opponent)
      as [w b] eqn:Hpol.
    rewrite step_game_equation. cbn zeta.
    unfold branch in Hbranch.
    destruct (move_result turn (move_state turn st (if turn then w st else b st)))
      as [r|] eqn:Hresult.
    + exact Hbranch.
    + specialize (IH (negb turn)
        (move_state turn st (if turn then w st else b st)) opponent).
      rewrite Hpol in IH. apply IH; [rewrite move_state_history; lia|exact Hbranch].
Qed.

Definition prevents_white (r : Result) : bool :=
  match r with WhiteWins => false | _ => true end.
Definition prevents_black (r : Result) : bool :=
  match r with BlackWins => false | _ => true end.

Definition black_nonloss_value : bool :=
  solve prevents_white false 125 true initial_state.
Definition white_nonloss_value : bool :=
  solve prevents_black true 125 true initial_state.

Definition WhiteForcedWin : Prop :=
  exists w : WhiteStrategy, forall b : BlackStrategy,
    outcome (play w b) = WhiteWins.
Definition BlackForcedWin : Prop :=
  exists b : BlackStrategy, forall w : WhiteStrategy,
    outcome (play w b) = BlackWins.

(** Keep conversion from attempting to unfold the entire 125-ply search while
    instantiating abstract soundness lemmas. This is not a computation claim. *)
Local Opaque solve.

Theorem black_nonloss_value_true :
  black_nonloss_value = true -> Goal.BlackNonLossFromEmpty.
Proof.
  intros H. exists (search_policy prevents_white false true). intros w.
  pose proof (solve_policy_sound prevents_white false true 125 true initial_state w
    eq_refl H) as Hsound.
  cbn [policies Bool.eqb] in Hsound. unfold play.
  destruct (outcome (step_game 125 true initial_state w
    (search_policy prevents_white false true))); cbn in Hsound; congruence.
Qed.

Theorem black_nonloss_value_false :
  black_nonloss_value = false -> WhiteForcedWin.
Proof.
  intros H. exists (search_policy prevents_white false false). intros b.
  pose proof (solve_policy_sound prevents_white false false 125 true initial_state b
    eq_refl H) as Hsound.
  cbn [policies Bool.eqb] in Hsound. unfold play.
  destruct (outcome (step_game 125 true initial_state
    (search_policy prevents_white false false) b)); cbn in Hsound; congruence.
Qed.

Theorem white_nonloss_value_true :
  white_nonloss_value = true -> Goal.WhiteNonLossFromEmpty.
Proof.
  intros H. exists (search_policy prevents_black true true). intros b.
  pose proof (solve_policy_sound prevents_black true true 125 true initial_state b
    eq_refl H) as Hsound.
  cbn [policies Bool.eqb] in Hsound. unfold play.
  destruct (outcome (step_game 125 true initial_state
    (search_policy prevents_black true true) b)); cbn in Hsound; congruence.
Qed.

Theorem white_nonloss_value_false :
  white_nonloss_value = false -> BlackForcedWin.
Proof.
  intros H. exists (search_policy prevents_black true false). intros w.
  pose proof (solve_policy_sound prevents_black true false 125 true initial_state w
    eq_refl H) as Hsound.
  cbn [policies Bool.eqb] in Hsound. unfold play.
  destruct (outcome (step_game 125 true initial_state w
    (search_policy prevents_black true false))); cbn in Hsound; congruence.
Qed.

Theorem black_nonloss_iff_value :
  Goal.BlackNonLossFromEmpty <-> black_nonloss_value = true.
Proof.
  split; [|exact black_nonloss_value_true]. intros [b Hb].
  destruct black_nonloss_value eqn:Hvalue; [reflexivity|].
  destruct (black_nonloss_value_false Hvalue) as [w Hw].
  specialize (Hb w). specialize (Hw b). congruence.
Qed.

Theorem white_nonloss_iff_value :
  Goal.WhiteNonLossFromEmpty <-> white_nonloss_value = true.
Proof.
  split; [|exact white_nonloss_value_true]. intros [w Hw].
  destruct white_nonloss_value eqn:Hvalue; [reflexivity|].
  destruct (white_nonloss_value_false Hvalue) as [b Hb].
  specialize (Hw b). specialize (Hb w). congruence.
Qed.

Theorem exact_draw_iff_values :
  Goal.ExactDraw <-> black_nonloss_value = true /\ white_nonloss_value = true.
Proof.
  unfold Goal.ExactDraw. rewrite black_nonloss_iff_value, white_nonloss_iff_value.
  reflexivity.
Qed.

(** A constructive three-way alternative, NOT a determination of which case
    holds. The unevaluated booleans are the exact remaining proof obligations. *)
Theorem game_value_alternatives :
  Goal.ExactDraw \/ WhiteForcedWin \/ BlackForcedWin.
Proof.
  destruct black_nonloss_value eqn:Hb.
  - destruct white_nonloss_value eqn:Hw.
    + left. apply exact_draw_iff_values. auto.
    + right. right. apply white_nonloss_value_false. exact Hw.
  - right. left. apply black_nonloss_value_false. exact Hb.
Qed.

Print Assumptions solve_policy_sound.
Print Assumptions black_nonloss_iff_value.
Print Assumptions white_nonloss_iff_value.
Print Assumptions exact_draw_iff_values.
Print Assumptions game_value_alternatives.
