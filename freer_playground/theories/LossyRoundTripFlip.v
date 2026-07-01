From mathcomp Require Import ssreflect ssrbool ssrnum ssralg reals
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib.
From FreerTheories Require Import FreerMonad.
From FreerTheories.lib Require Import FreerFlip.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Declare Scope lossy_flip_scope.
Local Open Scope lossy_flip_scope.

Notation "x <|| p ||> y" :=
  (choicef p x y)
  (at level 40, left associativity, y at next level) : lossy_flip_scope.

(**
  A lossy ping-pong round trip written directly over the FreerFlip effect.

  This file intentionally does not use [probMonad] or [bcoin].  Probabilistic
  choice is represented only by the freer effect [flipf].
 *)

Module LossyRoundTripFlip.

Section lossy_round_trip_flip.
  Context {R : realType}.
  Context {M : freerMonad (FlipEff R)}.

  Inductive packet := Ping | Pong.

  Inductive outcome :=
  | GotPong
  | LostPing
  | LostPong.

  Definition transmit (delivery : {prob R}) (m : packet) : M (option packet) :=
    flipf delivery >>= fun delivered =>
    Ret (if delivered then Some m else None).

  Definition client_send (delivery : {prob R}) : M (option packet) :=
    transmit delivery Ping.

  Definition server_reply (delivery : {prob R}) (incoming : option packet)
    : M (option packet) :=
    match incoming with
    | Some Ping => transmit delivery Pong
    | Some Pong => Ret None
    | None => Ret None
    end.

  Definition client_receive (incoming : option packet) : M outcome :=
    match incoming with
    | Some Pong => Ret GotPong
    | Some Ping => Ret LostPong
    | None => Ret LostPong
    end.

  Definition ping_pong_once (delivery : {prob R}) : M outcome :=
    client_send delivery >>= fun to_server =>
    match to_server with
    | Some Ping =>
        server_reply delivery to_server >>= client_receive
    | Some Pong => Ret LostPing
    | None => Ret LostPing
    end.

  Fixpoint ping_pong_retry (delivery : {prob R}) (fuel : nat) : M outcome :=
    match fuel with
    | O => ping_pong_once delivery
    | S fuel' =>
        ping_pong_once delivery >>= fun result =>
        match result with
        | GotPong => Ret GotPong
        | LostPing | LostPong => ping_pong_retry delivery fuel'
        end
    end.

  Definition delivery_probability (loss : {prob R}) : {prob R} :=
    loss%:num.~%:i01.

  Definition one_attempt_distribution (loss : {prob R}) : M outcome :=
    let delivery := delivery_probability loss in
    (Ret GotPong <|| delivery ||> Ret LostPong) <|| delivery ||> Ret LostPing.

  Definition round_trip_success_probability (loss : {prob R}) : {prob R} :=
    let delivery := delivery_probability loss in
    [p_of delivery, delivery].

  Definition one_attempt_failure_distribution (loss : {prob R}) : M outcome :=
    let delivery := delivery_probability loss in
    Ret LostPong <|| [q_of delivery, delivery] ||> Ret LostPing.

  Definition one_attempt_success_distribution (loss : {prob R}) : M outcome :=
    Ret GotPong
      <|| round_trip_success_probability loss ||>
    one_attempt_failure_distribution loss.

  Definition received_pong (result : outcome) : bool :=
    match result with
    | GotPong => true
    | LostPing | LostPong => false
    end.

  Definition observe_success (run : M outcome) : M bool :=
    run >>= fun result => Ret (received_pong result).

  Definition ping_pong_once_success (loss : {prob R}) : M bool :=
    observe_success (ping_pong_once (delivery_probability loss)).

  Definition ping_pong_retry_success (loss : {prob R}) (fuel : nat) : M bool :=
    observe_success (ping_pong_retry (delivery_probability loss) fuel).

  Fixpoint retry_success_probability (loss : {prob R}) (fuel : nat) : {prob R} :=
    match fuel with
    | O => round_trip_success_probability loss
    | S fuel' =>
        [s_of round_trip_success_probability loss,
              retry_success_probability loss fuel']
    end.

  Lemma transmit_certain delivery_packet :
    flip_rel (transmit 1%:i01 delivery_packet) (Ret (Some delivery_packet)).
  Proof.
    rewrite /transmit.
    eapply equiv_trans.
    - apply equiv_bind_congr.
      + exact: rflip1.
      + move=> delivered; exact: equiv_refl.
    rewrite bindretf.
    exact: equiv_refl.
  Qed.

  Lemma ping_pong_once_certain :
    flip_rel (ping_pong_once 1%:i01) (Ret GotPong).
  Proof.
    rewrite /ping_pong_once /client_send /server_reply /client_receive.
    eapply equiv_trans.
    - apply equiv_bind_congr.
      + exact: (transmit_certain Ping).
      + move=> to_server; exact: equiv_refl.
    rewrite bindretf.
    eapply equiv_trans.
    - apply equiv_bind_congr.
      + exact: (transmit_certain Pong).
      + move=> to_client; exact: equiv_refl.
    rewrite !bindretf.
    exact: equiv_refl.
  Qed.

  Lemma ping_pong_retry_certain fuel :
    flip_rel (ping_pong_retry 1%:i01 fuel) (Ret GotPong).
  Proof.
    elim: fuel => [|fuel _] /=.
    - exact: ping_pong_once_certain.
    eapply equiv_trans.
    - apply equiv_bind_congr.
      + exact: ping_pong_once_certain.
      + move=> result; exact: equiv_refl.
    rewrite bindretf.
    exact: equiv_refl.
  Qed.

End lossy_round_trip_flip.

End LossyRoundTripFlip.
