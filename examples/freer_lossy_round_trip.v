From mathcomp Require Import all_boot all_order all_algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Init effect freer free_choice.
From HB Require Import structures.

Import Order.TTheory Order.Syntax GRing.Theory Num.Theory.

Local Open Scope nat_scope.
Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope freer_flip_scope.

Inductive msg := Ping | Pong.

Inductive outcome := GotPong | LostPing | LostPong.

Section lossy_round_trip.
Context {R : realType} {M : choiceEqFreerMonad R}.

(* freerMonad (@FlipEff R)}. *)

Import FreerFlipDenote.
(* Import FreerFlipChoiceRel. *)

(* HB.about M. *)

Implicit Type (m : msg) (psucc : {prob R}).

Definition freer_transmit psucc m : M (option msg) :=
  Ret (Some m) <|| psucc ||> Ret None.

Lemma freer_transmit1 m : freer_transmit 1%:i01 m ≈ Ret (Some m).
Proof. exact: freer_choice1. Qed.

Definition client_send psucc : M (option msg) := freer_transmit psucc Ping.

Definition server_reply psucc (incoming : option msg) : M (option msg) :=
  if incoming is Some Ping then
    freer_transmit psucc Pong
  else
    Ret None.

Definition client_receive (incoming : option msg) : M outcome :=
  if incoming is Some Pong then
    Ret GotPong
  else
    Ret LostPong.

Definition ping_pong psucc : M outcome :=
  client_send psucc >>= fun to_server =>
    if to_server is Some Ping then
      server_reply psucc to_server >>= client_receive
    else
      Ret LostPing.

Lemma ping_pong1 : ping_pong 1%:i01 ≈ Ret GotPong.
Proof.
rewrite /ping_pong /client_send /server_reply /client_receive.
by rewrite freer_transmit1 bindretf freer_transmit1 bindretf.
Qed.

Fixpoint ping_pongs psucc (fuel : nat) : M outcome :=
  if fuel is fuel'.+1 then
    ping_pong psucc >>= fun result =>
                          if result is GotPong then
                            Ret GotPong
                          else
                            ping_pongs psucc fuel'
  else
    ping_pong psucc.

Lemma ping_pongs1 fuel : ping_pongs 1%:i01 fuel ≈ Ret GotPong.
Proof.
case: fuel => [|fuel].
  exact: ping_pong1.
rewrite /ping_pongs /ping_pong /client_send /server_reply /client_receive.
by rewrite freer_transmit1 bindretf freer_transmit1 bindretf bindretf.
Qed.

Lemma ping_pongsSE psucc fuel :
  ping_pongs psucc fuel.+1 ≈
  ping_pong psucc >>= fun oc =>
    if oc is GotPong then
      Ret GotPong
    else
      ping_pongs psucc fuel.
Proof. by []. Qed.

Definition freer_exchange psucc lostping lostpong : M outcome :=
  (Ret GotPong <|| psucc ||> lostpong) <|| psucc ||> lostping.

Definition freer_exchange_once psucc : M outcome :=
  freer_exchange psucc (Ret LostPing) (Ret LostPong).

Fixpoint freer_exchanges psucc fuel : M outcome :=
  if fuel is fuel'.+1 then
    freer_exchange psucc (freer_exchanges psucc fuel') (freer_exchanges psucc fuel')
  else
    freer_exchange_once psucc.

Lemma freer_exchangesSE psucc fuel :
  freer_exchanges psucc fuel.+1 ≈
  freer_exchange psucc (freer_exchanges psucc fuel) (freer_exchanges psucc fuel).
Proof. by []. Qed.

Lemma ping_pong_distribution psucc :
  ping_pong psucc ≈ freer_exchange_once psucc.
Proof.
rewrite /ping_pongs /ping_pong /client_send /server_reply /client_receive.
rewrite /freer_exchange_once /freer_exchange.
by repeat rewrite freer_choice_bindDl !bindretf.
Qed.

Lemma ping_pongs_freer_exchanges psucc fuel :
  ping_pongs psucc fuel ≈ freer_exchanges psucc fuel.
Proof.
elim: fuel => [|fuel IH].
  exact: ping_pong_distribution.
rewrite ping_pongsSE ping_pong_distribution freer_exchangesSE.
by rewrite /freer_exchange_once /freer_exchange !freer_choice_bindDl !bindretf IH.
Qed.

End lossy_round_trip.
