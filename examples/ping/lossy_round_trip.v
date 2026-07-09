(* Monae version poc *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnum ssralg reals sequences
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib proba_model.

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

Module LossyRoundTripMod.

Section lossy_round_trip_sec.
  Context {R : realType} {M : probMonad R}.

  Inductive packet := Ping | Pong.

  Inductive outcome :=
  | GotPong
  | LostPing
  | LostPong.

  Definition transmit (delivery : {prob R}) (m : packet) : M (option packet) :=
    Ret (Some m) <| delivery |> Ret None.

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
    | Some Ping => server_reply delivery to_server >>= client_receive
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

  Definition one_attempt_distribution (p : {prob R}) : M outcome :=
    (Ret GotPong <| p |> Ret LostPong) <| p |> Ret LostPing.

  Definition round_trip_success_probability (p : {prob R}) : {prob R} :=
    (* let delivery := loss%:num.~%:i01 in *)
    [p_of p, p].

  Definition retry_step_probability (delivery retry : {prob R}) : {prob R} :=
    [s_of (round_trip_success_probability delivery), retry].

Fixpoint retry_success_probability (loss : {prob R}) (fuel : nat) : {prob R} :=
  match fuel with
  | O => round_trip_success_probability loss
  | S fuel' =>
      retry_step_probability loss (retry_success_probability loss fuel')
  end.
  
  (* Definition one_attempt_failure_distribution (loss : {prob R}) : M outcome :=
    let delivery := loss%:num.~%:i01 in
    Ret LostPong <| [q_of delivery, delivery] |> Ret LostPing.

  Definition one_attempt_success_distribution (loss : {prob R}) : M outcome :=
    Ret GotPong
      <| round_trip_success_probability loss |>
    one_attempt_failure_distribution loss. *)

  Fixpoint retry_success_distribution (loss : {prob R}) (fuel : nat) : M outcome :=
  match fuel with 
  | O => one_attempt_distribution loss
  | S n => (Ret GotPong <| loss |> retry_success_distribution loss n) <| loss |>  retry_success_distribution loss n
  end.
 

  Definition success_event : pred outcome := fun result =>
    match result with
    | GotPong => true
    | LostPing | LostPong => false
    end.

  Definition success_of (run : M outcome) : M bool :=
    run >>= fun result => Ret (success_event result).

  Definition ping_pong_once_success (p : {prob R}) : M bool :=
    success_of (ping_pong_once p).

  Definition ping_pong_retry_success (p : {prob R}) (fuel : nat) : M bool :=
    success_of (ping_pong_retry p fuel).

  (* 1 message = 1 - p *)
  (* 1 exchange = 2 messages -> 1 exchange = (1 - p) * (1 - p) = (1 - p)^2 = q *)
  (* retry = 1 - (1 - q)^(n + 1) *)
  (* no_retry = 1 - (1 - q)^1 = 1 - (1 - q) = 1 - 1 - q = - (1 - p)^2 *)

  (* Fixpoint retry_success_probability (loss : {prob R}) (fuel : nat) : {prob R} :=
    match fuel with
    | O => round_trip_success_probability loss
    | S fuel' =>
        retry_step_probability loss (retry_success_probability loss fuel')
    end. *)

  Definition expected_attempts_before_success (loss : {prob R}) : R :=
    ((round_trip_success_probability loss)%:num)^-1.

  Definition expected_attempts_equation (success expected : R) : Prop :=
    expected = 1 + success.~ * expected.

  Ltac unfold_ping :=
    rewrite  /ping_pong_retry /ping_pong_once
            /client_send /server_reply /client_receive.
  Ltac unfold_success := 
    rewrite /ping_pong_retry_success /ping_pong_once_success
            /success_of /success_event.

  (* Ltac unfold_dist :=
    rewrite /delivery_probability
            /one_attempt_distribution
            /one_attempt_failure_distribution
            /one_attempt_success_distribution
            /round_trip_success_probability
            /retry_success_probability
            /expected_attempts_before_success
            /expected_attempts_equation. *)

  Lemma transmit_certain m :
    transmit 1%:i01 m = Ret (Some m) :> M _.
  Proof.
    by rewrite /transmit choice1.
  Qed.

  Lemma ping_pong_once_certain :
    ping_pong_once 1%:i01 = Ret GotPong :> M _.
  Proof.
    by unfold_ping; rewrite !transmit_certain !bindretf.
  Qed.

  Lemma ping_pong_retry_certain fuel :
    ping_pong_retry 1%:i01 fuel = Ret GotPong :> M _.
  Proof.
    by elim : fuel => /= [|n IH]; rewrite ping_pong_once_certain ?bindretf.
  Qed.

  Lemma ping_pong_once_distribution_shape (loss : {prob R}) :
    ping_pong_once (loss%:num.~%:i01) = one_attempt_distribution (loss%:num.~%:i01).
  Proof.
       by unfold_ping; rewrite /transmit choice_bindDl !bindretf choice_bindDl !bindretf.
  Qed.

  
  Lemma ping_pong_once_success_probability (loss : {prob R}) :
    ping_pong_once_success (loss%:num.~%:i01) = bcoin (round_trip_success_probability (loss%:num.~%:i01)).
  Proof.
     unfold_success; rewrite ping_pong_once_distribution_shape.
     rewrite /one_attempt_distribution /round_trip_success_probability /bcoin 
      !choice_bindDl !bindretf.

    set d := loss%:num.~%:i01. 
    have [->/=|d0] := eqVneq d 0%:i01.
    - by rewrite p_of_0s !choice0.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite p_of_1s choice1.
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    (* Give right the same form as left *)
    rewrite -[Ret false in RHS](choicemm [q_of d, d]).

    by rewrite choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
  Qed.

  Lemma bcoin_or_true (p q : {prob R}) :
    Ret true <| p |> bcoin q = bcoin [s_of p, q] :> M bool.
  Proof.
    by rewrite /bcoin choiceA choicemm.
  Qed.

  (* Lemma choice_idem_expand T (p : {prob R}) (x : M T) :
    x = x <| p |> x.
  Proof. by rewrite choicemm. Qed.

  Lemma retry_choice_step T (d : {prob R}) (x y : M T) :
    d != 0%:i01 -> d != 1%:i01 ->
    (x <| d |> y) <| d |> y = x <| [p_of d, d] |> y.
  Proof.
    move=> d0 d1.
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    rewrite [y in RHS](choicemm [q_of d, d]).
    by rewrite choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
  Qed.

  Lemma retry_bcoin_step (d retry : {prob R}) :
    d != 0%:i01 -> d != 1%:i01 ->
    (Ret true <| d |> bcoin retry) <| d |> bcoin retry =
      bcoin [s_of [p_of d, d], retry] :> M bool.
  Proof.
    by move=> d0 d1; rewrite bcoin_or_trueE (@retry_choice_step bool d (Ret true) (bcoin retry) d0 d1).
  Qed. *)

    Lemma ping_pong_retry_distribution_shape (loss : {prob R}) (fuel : nat) :
    ping_pong_retry (loss%:num.~%:i01) fuel = retry_success_distribution (loss%:num.~%:i01) fuel.
  Proof.
    elim : fuel => [|n].
    - exact: ping_pong_once_distribution_shape.
    unfold_ping; rewrite /transmit.
    by rewrite !choice_bindDl !bindretf !choice_bindDl !bindretf => ->.
  Qed.

  Fact retry0 : forall n, retry_success_probability (widen_itv 0%:itv) n = 0%:i01.
  Proof. 
    by elim=>//=[|n IH]; rewrite /retry_step_probability /round_trip_success_probability ?p_of_0s ?s_of_0q.
  Qed.

  Fact retry1 : forall n, retry_success_probability (widen_itv 1%:itv) n = 1%:i01.
  Proof. 
    by elim=>//=[|n IH]; rewrite /retry_step_probability /round_trip_success_probability ?p_of_1s ?s_of_1q.
  Qed.

  Fact retryd0 : forall p n, p = 0%:i01 -> retry_success_probability p n = 0%:i01.
  Proof. 
    by move=> p n ->; apply: retry0.
  Qed.

  Fact retryd1 : forall p n, p = 1%:i01 -> retry_success_probability p n = 1%:i01.
  Proof. 
    by move=> p n ->; apply: retry1.
  Qed.

  Lemma ping_pong_retry_success_probability (delivery : {prob R}) (fuel : nat) :
    ping_pong_retry_success (delivery%:num.~%:i01) fuel = bcoin (retry_success_probability (delivery%:num.~%:i01) fuel).
  Proof.
    elim : fuel => /= [|n].
    - exact: ping_pong_once_success_probability.
    unfold_success.
    rewrite !ping_pong_retry_distribution_shape.
    rewrite /retry_step_probability /round_trip_success_probability /=.
    
    rewrite !choice_bindDl !bindretf => ->. 

    set d := delivery%:num.~%:i01.
    
    have [->/=|d0] := eqVneq d 0%:i01.
    - by rewrite /bcoin p_of_0s s_of_0q retry0 !choice0.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite /bcoin p_of_1s s_of_1q retry1 !choice1.

    rewrite -(bcoin_or_true [p_of d, d] (retry_success_probability d n)).
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    rewrite -[bcoin (retry_success_probability d n) in RHS](choicemm [q_of d, d]).
    by rewrite choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
  Qed.

End lossy_round_trip_sec.
End LossyRoundTripMod.
