From mathcomp Require Import ssreflect ssrbool ssrnum ssralg reals
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib.
From FreerDPS Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Declare Scope impure_prob_scope.
Local Open Scope impure_prob_scope.

Notation "x <|| p ||> y" :=
  (prob_choice p x y)
  (at level 40, left associativity, y at next level) : impure_prob_scope.

(**
  A lossy ping-pong round trip written in FreeSpec's [impure] monad.

  This mirrors [freer_playground/theories/LossyRoundTripFlip.v], but the flip
  effect is now the main-theory [prob_interface] primitive [CanWork].
 *)

Module LossyRoundTripImpure.

Section lossy_round_trip_impure.
  Context {R : realType}.
  Context {ix : interface}.
  Context `{Provide ix (@prob_interface R)}.
  Context {im : impureMonad ix}.

  Inductive packet := Ping | Pong.

  Inductive outcome :=
  | GotPong
  | LostPing
  | LostPong.

  Definition transmit (delivery : {prob R}) (m : packet)
    : im (option packet) :=
    bind (prob_flip delivery) (fun delivered =>
      Ret (if delivered then Some m else None)).

  Definition client_send (delivery : {prob R}) : im (option packet) :=
    transmit delivery Ping.

  Definition server_reply (delivery : {prob R}) (incoming : option packet)
    : im (option packet) :=
    match incoming with
    | Some Ping => transmit delivery Pong
    | Some Pong => Ret None
    | None => Ret None
    end.

  Definition client_receive (incoming : option packet) : im outcome :=
    match incoming with
    | Some Pong => Ret GotPong
    | Some Ping => Ret LostPong
    | None => Ret LostPong
    end.

  Definition ping_pong_once (delivery : {prob R}) : im outcome :=
    bind (client_send delivery) (fun to_server =>
      match to_server with
      | Some Ping =>
          bind (server_reply delivery to_server) client_receive
      | Some Pong => Ret LostPing
      | None => Ret LostPing
      end).

  Fixpoint ping_pong_retry (delivery : {prob R}) (fuel : nat)
    : im outcome :=
    match fuel with
    | O => ping_pong_once delivery
    | S fuel' =>
        bind (ping_pong_once delivery) (fun result =>
          match result with
          | GotPong => Ret GotPong
          | LostPing | LostPong => ping_pong_retry delivery fuel'
          end)
    end.

  Definition delivery_probability (loss : {prob R}) : {prob R} :=
    loss%:num.~%:i01.

  Definition one_attempt_distribution (loss : {prob R}) : im outcome :=
    let delivery := delivery_probability loss in
    (Ret GotPong <|| delivery ||> Ret LostPong)
      <|| delivery ||> Ret LostPing.

  Definition round_trip_success_probability (loss : {prob R}) : {prob R} :=
    let delivery := delivery_probability loss in
    [p_of delivery, delivery].

  Definition one_attempt_failure_distribution (loss : {prob R})
    : im outcome :=
    let delivery := delivery_probability loss in
    Ret LostPong <|| [q_of delivery, delivery] ||> Ret LostPing.

  Definition one_attempt_success_distribution (loss : {prob R})
    : im outcome :=
    Ret GotPong
      <|| round_trip_success_probability loss ||>
    one_attempt_failure_distribution loss.

  Definition received_pong (result : outcome) : bool :=
    match result with
    | GotPong => true
    | LostPing | LostPong => false
    end.

  Definition observe_success (run : im outcome) : im bool :=
    bind run (fun result => Ret (received_pong result)).

  Definition ping_pong_once_success (loss : {prob R}) : im bool :=
    observe_success (ping_pong_once (delivery_probability loss)).

  Definition ping_pong_retry_success (loss : {prob R}) (fuel : nat)
    : im bool :=
    observe_success (ping_pong_retry (delivery_probability loss) fuel).

  Fixpoint retry_success_probability (loss : {prob R}) (fuel : nat) : {prob R} :=
    match fuel with
    | O => round_trip_success_probability loss
    | S fuel' =>
        [s_of round_trip_success_probability loss,
              retry_success_probability loss fuel']
    end.

  Lemma transmit_certain delivery_packet :
    prob_rel _ (transmit 1%:i01 delivery_packet) (Ret (Some delivery_packet)).
  Proof.
    rewrite /transmit.
    apply: prob_rel_trans.
    - apply: prob_rel_bind_congr.
      + exact: rprob1.
      + move=> delivered; exact: prob_rel_refl.
    rewrite bindretf.
    exact: prob_rel_refl.
  Qed.

  Lemma ping_pong_once_certain :
    prob_rel _ (ping_pong_once 1%:i01) (Ret GotPong).
  Proof.
    rewrite /ping_pong_once /client_send /server_reply /client_receive.
    apply: prob_rel_trans.
    - apply: prob_rel_bind_congr.
      + exact: (transmit_certain Ping).
      + move=> to_server; exact: prob_rel_refl.
    rewrite bindretf.
    change (prob_rel _
      (bind (transmit 1%:i01 Pong) client_receive)
      (Ret GotPong)).
    apply: prob_rel_trans.
    - apply: prob_rel_bind_congr.
      + exact: (transmit_certain Pong).
      + move=> to_client; exact: prob_rel_refl.
    rewrite bindretf.
    exact: prob_rel_refl.
  Qed.

  Lemma ping_pong_retry_certain fuel :
    prob_rel _ (ping_pong_retry 1%:i01 fuel) (Ret GotPong).
  Proof.
    elim: fuel => [|fuel _] /=.
    - exact: ping_pong_once_certain.
    change (prob_rel _
      (bind (ping_pong_once 1%:i01) (fun result =>
        match result with
        | GotPong => Ret GotPong
        | LostPing | LostPong => ping_pong_retry 1%:i01 fuel
        end))
      (Ret GotPong)).
    apply: prob_rel_trans.
    - apply: prob_rel_bind_congr.
      + exact: ping_pong_once_certain.
      + move=> result; exact: prob_rel_refl.
    rewrite bindretf.
    exact: prob_rel_refl.
  Qed.

End lossy_round_trip_impure.

End LossyRoundTripImpure.
