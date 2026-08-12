From mathcomp Require Import all_boot interval_inference.
From mathcomp Require Import ssrnum ssralg reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From HB Require Import structures.

Import GRing.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope monae_scope.

Inductive msg := Ping | Pong.

Inductive outcome := GotPong | LostPing | LostPong.

Section syntactic_sugar_for_probabilities.
Context {R : realType}.

Definition p_ex_once (p : {prob R}) : {prob R} := [p_of p, p].

Lemma p_ex_onceE p : p_ex_once p = [p_of p, p].
Proof. by []. Qed.

Definition p_ex (psucc retry : {prob R}) : {prob R} :=
  [s_of (p_ex_once psucc), retry].

Fixpoint p_exs (loss : {prob R}) n : {prob R} :=
  if n is n'.+1 then p_ex loss (p_exs loss n') else p_ex_once loss.

Lemma p_exsE psucc n :
  p_exs psucc n =
    if n is n'.+1 then p_ex psucc (p_exs psucc n')
    else p_ex_once psucc.
Proof. by case: n. Qed.

Lemma p_exE psucc retry :
  p_ex psucc retry = [s_of (p_ex_once psucc), retry].
Proof. by []. Qed.

Fact retry0 : forall n, p_exs (widen_itv 0%:itv) n = 0%:i01.
Proof.
by elim=> [|n IH];
  rewrite p_exsE ?p_exE p_ex_onceE p_of_0s // s_of_0q IH.
Qed.

Fact retry1 : forall n, p_exs (widen_itv 1%:itv) n = 1%:i01.
Proof.
by case=> [|n];
  rewrite p_exsE ?p_exE p_ex_onceE p_of_1s // s_of_1q.
Qed.

End syntactic_sugar_for_probabilities.

Section ping_pong_protocol.
Context {R : realType} {M : monad} {transmit : {prob R} -> msg -> M (option msg)}.
(* Variable transmit : {prob R} -> msg -> M (option msg). *)
Implicit Types (m : msg) (psucc : {prob R}).

Definition client_send (psucc: {prob R}) : M (option msg) := transmit psucc Ping.

Definition server_reply psucc (incoming : option msg) : M (option msg) :=
  if incoming is Some Ping then transmit psucc Pong else Ret None.

Definition client_receive (incoming : option msg) : M outcome :=
  if incoming is Some Pong then Ret GotPong else Ret LostPong.

Definition ping_pong
  psucc : M outcome
   :=
  client_send psucc >>= fun to_server =>
    if to_server is Some Ping then
      server_reply psucc to_server >>= client_receive
    else
      Ret LostPing.

Fixpoint ping_pongs psucc (fuel : nat) : M outcome :=
  if fuel is fuel'.+1 then
    ping_pong psucc >>= fun result =>
      if result is GotPong then Ret GotPong else ping_pongs psucc fuel'
  else
    ping_pong psucc.

Lemma ping_pongsE psucc fuel :
  ping_pongs psucc fuel =
    if fuel is fuel'.+1 then
      ping_pong psucc >>= fun result =>
        if result is GotPong then Ret GotPong else ping_pongs psucc fuel'
    else
      ping_pong psucc.
Proof. by case: fuel. Qed.

Lemma ping_pongsSE psucc fuel :
  ping_pongs psucc fuel.+1 =
    ping_pong psucc >>= fun result =>
      if result is GotPong then Ret GotPong else ping_pongs psucc fuel.
Proof. by []. Qed.

Definition success_event : pred outcome := fun result =>
  if result is GotPong then true else false.

Definition success_of (run : M outcome) : M bool :=
  run >>= fun result => Ret (success_event result).

Definition ping_pong_success p : M bool := success_of (ping_pong p).

Definition ping_pongs_success p fuel : M bool :=
  success_of (ping_pongs p fuel).

Lemma success_eventE result :
  success_event result = if result is GotPong then true else false.
Proof. by case: result. Qed.

Lemma success_ofE run :
  success_of run = (run >>= fun result => Ret (success_event result)).
Proof. by []. Qed.

Lemma ping_pong_successE p :
  ping_pong_success p = success_of (ping_pong p).
Proof. by []. Qed.

Lemma ping_pongs_successE p fuel :
  ping_pongs_success p fuel = success_of (ping_pongs p fuel).
Proof. by []. Qed.

End ping_pong_protocol.

Section ping_pong_distribution.
Context {R : realType} {M : monad} {choose : {prob R} -> forall A, M A -> M A -> M A}.

Definition exchange psucc lostping lostpong : M outcome :=
  choose psucc  _ (choose psucc _ (Ret GotPong) lostpong) lostping.

Definition exchange_once psucc : M outcome :=
  exchange psucc (Ret LostPing) (Ret LostPong).

Fixpoint exchanges psucc fuel : M outcome :=
  if fuel is fuel'.+1 then
    exchange psucc (exchanges psucc fuel') (exchanges psucc fuel')
  else
    exchange_once psucc.

Lemma exchangesSE psucc fuel :
  exchanges psucc fuel.+1 =
    exchange psucc (exchanges psucc fuel) (exchanges psucc fuel).
Proof. by []. Qed.

End ping_pong_distribution.
