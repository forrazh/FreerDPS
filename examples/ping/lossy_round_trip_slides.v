From mathcomp Require Import ssreflect ssrbool eqtype ssrnum ssralg reals
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib proba_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope proba_monad_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

(**
  A slide-sized lossy ping-pong model.

  Each network hop succeeds with probability [delivery].
  A round trip succeeds when the ping and the pong are both delivered.
 *)
Module LossyRoundTripSlides.

Section lossy_round_trip.
  Context {R : realType}.
  Context {M : probMonad R}.

  Inductive packet := Ping | Pong.

  Inductive outcome :=
  | GotPong
  | LostPing
  | LostPong.

  Definition transmit (delivery : {prob R}) (p : packet)
    : M (option packet) :=
    bcoin delivery >>= fun delivered =>
    Ret (if delivered then Some p else None).

  Definition ping_pong_once (delivery : {prob R}) : M outcome :=
    transmit delivery Ping >>= fun to_server =>
    match to_server with
    | Some Ping =>
        transmit delivery Pong >>= fun to_client =>
        match to_client with
        | Some Pong => Ret GotPong
        | Some Ping | None => Ret LostPong
        end
    | Some Pong | None => Ret LostPing
    end.

  Definition delivery_probability (loss : {prob R}) : {prob R} :=
    loss%:num.~%:i01.

  Definition one_attempt_distribution (loss : {prob R}) : M outcome :=
    let delivery := delivery_probability loss in
    (Ret GotPong <| delivery |> Ret LostPong) <| delivery |> Ret LostPing.

  Definition success_probability (loss : {prob R}) : {prob R} :=
    let delivery := delivery_probability loss in
    [p_of delivery, delivery].

  Lemma ping_pong_once_distribution (loss : {prob R}) :
    ping_pong_once (delivery_probability loss) =
    one_attempt_distribution loss.
  Proof.
    rewrite /ping_pong_once /one_attempt_distribution
            /delivery_probability /transmit /bcoin.
    set delivery := loss%:num.~%:i01.
    rewrite (choice_bindDl delivery) !bindretf.
    rewrite (choice_bindDl delivery) !bindretf.
    rewrite (choice_bindDl delivery) !bindretf.
    by rewrite (choice_bindDl delivery) !bindretf.
  Qed.

  Lemma success_probabilityE (loss : {prob R}) :
    (success_probability loss)%:num =
    (delivery_probability loss)%:num *
    (delivery_probability loss)%:num :> R.
  Proof. by rewrite /success_probability p_of_rsE. Qed.

  Definition expected_attempts (loss : {prob R}) : R :=
    ((success_probability loss)%:num)^-1.

  Lemma expected_attemptsE (loss : {prob R}) :
    expected_attempts loss =
    ((delivery_probability loss)%:num *
     (delivery_probability loss)%:num)^-1.
  Proof. by rewrite /expected_attempts success_probabilityE. Qed.

  Lemma expected_attempts_pdf (loss : {prob R}) :
    expected_attempts loss = (loss%:num.~ * loss%:num.~)^-1.
  Proof. by rewrite expected_attemptsE /delivery_probability. Qed.

End lossy_round_trip.

End LossyRoundTripSlides.
