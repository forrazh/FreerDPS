From mathcomp Require Import all_boot boolp interval_inference reals ssrnum
ssralg.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib.
From FreerDPS Require Import Impure.
From FreerExamples Require Import equational_reasoning.freer_choice.

Import FreerFuns freer_choice.FreerFlipModel.
Import GRing.Theory.

Generalizable All Variables.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope freer_flip_scope.

Module FreerLossyRoundTrip.

Section lossy_round_trip.
Variable R : realType.
Variable M : freerMonad (FlipEff R).

Local Notation "x <|| p ||> y" :=
(choicef R M p x y)
(at level 40, left associativity, y at next level).

Local Notation "a === b" :=
(choice_rel R M a b)
(at level 70).

Inductive packet := Ping | Pong.

Inductive outcome := GotPong | LostPing | LostPong.
Definition transmit (delivery : {prob R}) (m : packet) : M (option packet) :=
  Ret (Some m) <|| delivery ||> Ret None.

Definition client_send (delivery : {prob R}) : M (option packet) :=
  transmit delivery Ping.

Definition server_reply (delivery : {prob R}) (incoming : option packet)
  : M (option packet) :=
match incoming with
| Some Ping => transmit delivery Pong
| Some Pong | None => Ret None
end.

Definition client_receive (incoming : option packet)
  : M outcome :=
match incoming with
| Some Pong => Ret GotPong
| Some Ping | None => Ret LostPong
end.

Definition ping_pong_once (delivery : {prob R})
  : M outcome :=
client_send delivery >>= fun to_server =>
match to_server with
| Some Ping => server_reply delivery to_server >>= client_receive
| Some Pong | None => Ret LostPing
end.

Fixpoint ping_pong_retry (delivery : {prob R}) (fuel : nat)
  : M outcome :=
match fuel with
| O => ping_pong_once delivery
| S fuel' => ping_pong_once delivery >>= fun result =>
  match result with
  | GotPong => Ret GotPong
  | LostPing | LostPong => ping_pong_retry delivery fuel'
  end
end.

Definition one_attempt_distribution (delivery : {prob R})
  : M outcome :=
(Ret GotPong <|| delivery ||> Ret LostPong) <|| delivery ||> Ret LostPing.

Fixpoint retry_success_distribution (delivery : {prob R}) (fuel : nat)
  : M outcome :=
match fuel with
| O => one_attempt_distribution delivery
| S fuel' =>
  (Ret GotPong <|| delivery ||> retry_success_distribution delivery fuel')
    <|| delivery ||> retry_success_distribution delivery fuel'
end.

Lemma f_ping_pong_retrySE delivery fuel
  : ping_pong_retry delivery fuel.+1
    === ping_pong_once delivery >>= fun result =>
  match result with
  | GotPong => Ret GotPong
  | LostPing | LostPong => ping_pong_retry delivery fuel
  end.
Proof. exact: equiv_refl. Qed.

Lemma f_retry_success_distributionSE delivery fuel
  : retry_success_distribution delivery fuel.+1
    === (Ret GotPong <|| delivery ||> retry_success_distribution delivery fuel)
  <|| delivery ||> retry_success_distribution delivery fuel.
Proof. exact: equiv_refl. Qed.

Lemma f_transmit1 m
  : transmit 1%:i01 m === Ret (Some m).
Proof. exact: rchoice1. Qed.

Lemma f_ping_pong_once1 : ping_pong_once 1%:i01 === Ret GotPong.
Proof.
apply: equiv_bind_congr_trans.
- exact: f_transmit1.
- by move=>?; exact: equiv_refl.
rewrite bindretf; apply: equiv_bind_congr_trans.
- exact: f_transmit1.
- by move=> ?; exact: equiv_refl.
by rewrite bindretf; exact: equiv_refl.
Qed.

Lemma f_ping_pong_retry1 fuel :
ping_pong_retry 1%:i01 fuel === Ret GotPong.
Proof.
case: fuel => [|fuel].
- exact: f_ping_pong_once1.
apply:equiv_bind_congr_trans.
+ exact: f_ping_pong_once1.
+ by move=> ?; exact: equiv_refl.
by rewrite bindretf; exact: equiv_refl.
Qed.

Lemma f_ping_pong_once_distribution delivery :
ping_pong_once delivery === one_attempt_distribution delivery.
Proof.
apply: rchoice_bindDl_trans; rewrite !bindretf.
apply: equiv_bind_congr.
- exact: equiv_refl.
- case.
  + by apply/rchoice_bindDl_trans; rewrite !bindretf; exact: equiv_refl.
  + exact: equiv_refl.
Qed.

Lemma f_ping_pong_retry_distribution delivery fuel :
ping_pong_retry delivery fuel === retry_success_distribution delivery fuel.
Proof.
elim: fuel => [|fuel IH].
- exact: f_ping_pong_once_distribution.
apply: equiv_trans.
- exact: f_ping_pong_retrySE.
apply: equiv_bind_congr_trans.
- exact: f_ping_pong_once_distribution.
- by move=>?; exact: equiv_refl.
apply: rchoice_bindDl_choice_congr; last first.
- by rewrite bindretf; exact: IH.
by apply: rchoice_bindDl_choice_congr;
  rewrite bindretf; [exact: equiv_refl|exact: IH].
Qed.

End lossy_round_trip.
End FreerLossyRoundTrip.
