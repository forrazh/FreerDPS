(* Monae version poc *)
From mathcomp Require Import ssreflect ssrbool eqtype interval_inference ssrnum
  ssralg.
From mathcomp Require Import reals sequences.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib proba_model.
From FreerDPS Require Import freer_lossy_round_trip.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope proba_monad_scope.
Local Open Scope mprog.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

Import GRing.Theory.

Section syntactic_sugar_for_probabilities.
Context {R : realType}.

  (* q^2 *)
Definition round_trip_success_probability (p : {prob R}) : {prob R} :=
  (* let psucc := loss%:num.~%:i01 in *)
  [p_of p, p].

Lemma round_trip_success_probabilityE p :
  round_trip_success_probability p = [p_of p, p].
Proof. by []. Qed.

Definition retry_step_probability (psucc retry : {prob R}) : {prob R} :=
  [s_of (round_trip_success_probability psucc), retry].

(* q ^ n *)
Fixpoint retry_success_probability (loss : {prob R}) n : {prob R} :=
  match n with
  | O => round_trip_success_probability loss
  | S n' =>
      retry_step_probability loss (retry_success_probability loss n')
  end.

Lemma retry_success_probabilityE psucc n :
  retry_success_probability psucc n =
    match n with
    | O => round_trip_success_probability psucc
    | S n' => retry_step_probability psucc (retry_success_probability psucc n')
    end.
Proof. by case: n. Qed.

Lemma retry_step_probabilityE psucc retry :
  retry_step_probability psucc retry =
    [s_of (round_trip_success_probability psucc), retry].
Proof. by []. Qed.

Lemma retry_success_probability_stepE psucc n :
  retry_success_probability psucc (S n) =
    [s_of [p_of psucc, psucc], retry_success_probability psucc n].
Proof.
  by rewrite retry_success_probabilityE retry_step_probabilityE
     round_trip_success_probabilityE.
Qed.

Fact retry0 : forall n, retry_success_probability (widen_itv 0%:itv) n = 0%:i01.
Proof.
  elim=> [|n IH].
  - by rewrite retry_success_probabilityE round_trip_success_probabilityE p_of_0s.
  by rewrite retry_success_probability_stepE p_of_0s s_of_0q IH.
Qed.

Fact retry1 : forall n, retry_success_probability (widen_itv 1%:itv) n = 1%:i01.
Proof.
case=> [|n].
- by rewrite retry_success_probabilityE round_trip_success_probabilityE p_of_1s.
by rewrite retry_success_probability_stepE p_of_1s s_of_1q.
Qed.

End syntactic_sugar_for_probabilities.

Section about_probMonad.
Context {R : realType} {M : probMonad R}.

Lemma bcoinE p : bcoin p = (Ret true <| p |> Ret false :> M bool).
Proof. by rewrite /bcoin. Qed.

Fact bcoin_or_true (p q : {prob R}) :
  Ret true <| p |> bcoin q = bcoin [s_of p, q] :> M bool.
Proof. by rewrite !bcoinE choiceA choicemm. Qed.

End about_probMonad.

Section lossy_round_trip_sec.
Context {R : realType} {M : probMonad R}.
Implicit Types (psucc : {prob R}) (m : msg).

Definition prob_transmit psucc m : M (option msg) :=
  Ret (Some m) <| psucc |> Ret None.

Definition client_send psucc : M (option msg) :=
  prob_transmit psucc Ping.

Definition server_reply (psucc : {prob R}) (incoming : option msg)
    : M (option msg) :=
  match incoming with
  | Some Ping => prob_transmit psucc Pong
  | Some Pong => Ret None
  | None => Ret None
  end.

Definition client_receive (incoming : option msg) : M outcome :=
  match incoming with
  | Some Pong => Ret GotPong
  | Some Ping => Ret LostPong
  | None => Ret LostPong
  end.

Definition ping_pong_once psucc : M outcome :=
  client_send psucc >>= fun to_server =>
  match to_server with
  | Some Ping => server_reply psucc to_server >>= client_receive
  | Some Pong => Ret LostPing
  | None => Ret LostPing
  end.

Fixpoint ping_pong_retry (psucc : {prob R}) (fuel : nat) : M outcome :=
  match fuel with
  | O => ping_pong_once psucc
  | S fuel' =>
      ping_pong_once psucc >>= fun result =>
      match result with
      | GotPong => Ret GotPong
      | LostPing | LostPong => ping_pong_retry psucc fuel'
      end
  end.

  (* --- Event distribution --- *)
  Definition prob_exchange (p : {prob R}) : M outcome :=
    (Ret GotPong <| p |> Ret LostPong) <| p |> Ret LostPing.

  Fixpoint retry_success_distribution (loss : {prob R}) (n : nat) : M outcome :=
    match n with
    | O => prob_exchange loss
    | S n' =>
        (Ret GotPong <| loss |> retry_success_distribution loss n') <| loss |>
        retry_success_distribution loss n'
    end.

  (* --- Event coercion --- *)

  Definition success_event : pred outcome := fun result =>
    match result with
    | GotPong => true
    | LostPing | LostPong => false
    end.

  (* Mapping to bcoin equiv *)
  Definition success_of (run : M outcome) : M bool :=
    run >>= fun result => Ret (success_event result).

  Definition ping_pong_once_success (p : {prob R}) : M bool :=
    success_of (ping_pong_once p).

  Definition ping_pong_retry_success (p : {prob R}) (fuel : nat) : M bool :=
    success_of (ping_pong_retry p fuel).

  (* --- Unfolding lemmas --- *)

  Lemma prob_transmitE psucc m :
    prob_transmit psucc m = (Ret (Some m) <| psucc |> Ret None :> M _).
  Proof. by []. Qed.

  Lemma client_sendE psucc :
    client_send psucc = prob_transmit psucc Ping.
  Proof. by []. Qed.

  Lemma server_replyE psucc incoming :
    server_reply psucc incoming =
      match incoming with
      | Some Ping => prob_transmit psucc Pong
      | Some Pong | None => Ret None
      end.
  Proof. by case: incoming => [[]|]. Qed.

  Lemma client_receiveE incoming :
    client_receive incoming =
      Ret match incoming with
          | Some Pong => GotPong
          | Some Ping | None => LostPong
          end.
  Proof. by case: incoming => [[]|]. Qed.

  Lemma ping_pong_onceE psucc :
    ping_pong_once psucc =
      client_send psucc >>= fun to_server =>
      match to_server with
      | Some Ping =>
          server_reply psucc to_server >>= client_receive
      | Some Pong | None => Ret LostPing
      end.
  Proof. by []. Qed.

  Lemma ping_pong_retryE psucc fuel :
    ping_pong_retry psucc fuel =
      match fuel with
      | O => ping_pong_once psucc
      | S fuel' =>
          ping_pong_once psucc >>= fun result =>
          match result with
          | GotPong => Ret GotPong
          | LostPing | LostPong => ping_pong_retry psucc fuel'
          end
      end.
  Proof. by case: fuel. Qed.

  Lemma ping_pong_retry_stepE psucc fuel :
    ping_pong_retry psucc (S fuel) =
      (Ret GotPong <| psucc |> ping_pong_retry psucc fuel) <| psucc |>
      ping_pong_retry psucc fuel.
  Proof.
    rewrite ping_pong_retryE ping_pong_onceE client_sendE !prob_transmitE.
    rewrite !choice_bindDl !bindretf server_replyE !prob_transmitE.
    by rewrite !choice_bindDl !bindretf.
  Qed.



  Lemma prob_exchangeE p :
    prob_exchange p =
      (Ret GotPong <| p |> Ret LostPong) <| p |> Ret LostPing :> M _.
  Proof. by []. Qed.

  Lemma retry_success_distributionE loss n :
    retry_success_distribution loss n =
      match n with
      | O => prob_exchange loss
      | S n' =>
          (Ret GotPong <| loss |> retry_success_distribution loss n') <| loss |>
          retry_success_distribution loss n'
      end.
  Proof. by case: n. Qed.

  Lemma success_eventE result :
    success_event result =
      match result with
      | GotPong => true
      | LostPing | LostPong => false
      end.
  Proof. by case: result. Qed.

  Lemma success_ofE run :
    success_of run = (run >>= fun result => Ret (success_event result)).
  Proof. by []. Qed.

  Lemma ping_pong_once_successE p :
    ping_pong_once_success p = success_of (ping_pong_once p).
  Proof. by []. Qed.

  Lemma ping_pong_retry_successE p fuel :
    ping_pong_retry_success p fuel = success_of (ping_pong_retry p fuel).
  Proof. by []. Qed.

  Lemma ping_pong_retry_success_stepE p fuel :
    ping_pong_retry_success p (S fuel) =
      (Ret true <| p |> ping_pong_retry_success p fuel) <| p |>
      ping_pong_retry_success p fuel.
  Proof.
    rewrite ping_pong_retry_successE success_ofE ping_pong_retry_stepE.
    rewrite !choice_bindDl !bindretf success_eventE.
    by rewrite -!success_ofE -!ping_pong_retry_successE.
  Qed.

  (* === Proofs === *)

  (* p = 1 *)

Fact prob_transmit_certain m : prob_transmit 1%:i01 m = Ret (Some m) :> M _.
Proof.
  by rewrite prob_transmitE choice1.
Qed.

Fact ping_pong_once_certain : ping_pong_once 1%:i01 = Ret GotPong :> M _.
Proof.
  by rewrite ping_pong_onceE client_sendE prob_transmit_certain bindretf
             server_replyE prob_transmit_certain bindretf client_receiveE.
Qed.

Fact ping_pong_retry_certain fuel :
  ping_pong_retry 1%:i01 fuel = Ret GotPong :> M _.
Proof.
  by elim : fuel => [|n IH];
     rewrite ping_pong_retryE ping_pong_once_certain ?bindretf.
Qed.

  (* == One round == *)

  Lemma ping_pong_once_distribution_shape (loss : {prob R}) :
    ping_pong_once (loss%:num.~%:i01) = prob_exchange (loss%:num.~%:i01).
  Proof.
    by rewrite ping_pong_onceE prob_exchangeE client_sendE !prob_transmitE
               !choice_bindDl !bindretf server_replyE !prob_transmitE
               !choice_bindDl !bindretf client_receiveE.
  Qed.

  Lemma ping_pong_once_success_probability (loss : {prob R}) :
    ping_pong_once_success (loss%:num.~%:i01) =
      bcoin (round_trip_success_probability (loss%:num.~%:i01)).
  Proof.
    rewrite ping_pong_once_successE success_ofE ping_pong_once_distribution_shape.
    rewrite prob_exchangeE round_trip_success_probabilityE bcoinE
            !choice_bindDl !bindretf !success_eventE.

    set d := loss%:num.~%:i01.
    have [->/=|d0] := eqVneq d 0%:i01.
    - by rewrite p_of_0s !choice0.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite p_of_1s choice1.
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    (* Give RHS the same form as LHS *)
    rewrite -[Ret false in RHS](choicemm [q_of d, d]).

    by rewrite choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
  Qed.

  (* == Multiple rounds *)

  Lemma ping_pong_retry_distribution_shape (loss : {prob R}) (fuel : nat) :
    ping_pong_retry (loss%:num.~%:i01) fuel = retry_success_distribution (loss%:num.~%:i01) fuel.
  Proof.
    elim : fuel => [|n IH].
    - exact: ping_pong_once_distribution_shape.
    by rewrite ping_pong_retry_stepE retry_success_distributionE IH.
  Qed.

  Theorem ping_pong_retry_success_probability psucc (fuel : nat) :
    ping_pong_retry_success (psucc%:num.~%:i01) fuel =
      bcoin (retry_success_probability (psucc%:num.~%:i01) fuel).
  Proof.
    elim : fuel => [|n].
    - exact: ping_pong_once_success_probability.
    rewrite ping_pong_retry_success_stepE retry_success_probability_stepE => ->.

    set d := psucc%:num.~%:i01.

    have [->/=|d0] := eqVneq d 0%:i01.
    - by rewrite !bcoinE p_of_0s s_of_0q retry0 !choice0.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite !bcoinE p_of_1s s_of_1q retry1 !choice1.

    rewrite -(bcoin_or_true [p_of d, d] (retry_success_probability d n)).
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    rewrite -[bcoin (retry_success_probability d n) in RHS](choicemm [q_of d, d]).
    by rewrite choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
  Qed.

End lossy_round_trip_sec.
