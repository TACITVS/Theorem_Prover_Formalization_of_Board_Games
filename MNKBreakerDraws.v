(** * MNKBreakerDraws.v: Draws from Checked Breaker Strategies

    A Breaker strategy that stops Maker for ever, checked by [check_br]
    (MNKBreakerCert.v), proves a draw of the strong game
    ([mnk_breaker_win_draw]).  The embedding theorems of MNKMakerBreaker.v
    then spread it to every board that fits inside, either way round, and to
    every longer line ([mnk_breaker_win_family]).

    Main results:
      - [mnk_5_4_4_breaker_wins]: Breaker wins the Maker-Breaker game on the
        5 x 4 board with 4 in a row (a 381-position certificate from
        solver/breaker_cert.c, in MNKBreakerCerts.v).
      - [mnk_5_4_4_draw]: (5, 4, 4) is a draw.
      - [mnk_draw_inside_5_4]: every (m, n, k) game whose board fits inside
        5 x 4, either way round, with k >= 4 is a draw.

    Zero axioms, zero admits. *)

From Stdlib Require Import List Arith Lia.
From MNK Require Import MNKBoard MNKGame MNKErdosSelfridge MNKMakerBreaker.
From MNK Require Import MNKBreakerCert MNKBreakerCerts.

Theorem mnk_5_4_4_breaker_wins : forall d,
  ~ maker_wins (gen_lines 5 4 4) P1 d (empty_board (5 * 4)).
Proof.
  apply (check_br_draw _ _ (gen_lines_nodup 5 4 4) br_cert_5_4_4_draw).
  vm_compute. reflexivity.
Qed.

Theorem mnk_5_4_4_draw : game_is_draw (gen_lines 5 4 4) (empty_board (5 * 4)).
Proof. apply mnk_breaker_win_draw. exact mnk_5_4_4_breaker_wins. Qed.

Theorem mnk_draw_inside_5_4 : forall m n k,
  ((m <= 5 /\ n <= 4) \/ (m <= 4 /\ n <= 5)) -> 4 <= k ->
  game_is_draw (gen_lines m n k) (empty_board (m * n)).
Proof.
  intros m n k Hfit Hk.
  apply (mnk_breaker_win_family 5 4 4 m n k); [exact Hfit | exact Hk |].
  exact mnk_5_4_4_breaker_wins.
Qed.
