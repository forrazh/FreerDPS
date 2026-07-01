From mathcomp Require Import ssreflect ssrbool eqtype ssrnum ssralg reals
  interval_inference.
From mathcomp Require Import finmap.
From infotheo Require Import realType_ext convex fsdist.
From monae Require Import preamble hierarchy monad_lib proba_lib proba_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope proba_monad_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

Import GRing.Theory.

(**
  A tiny probabilistic model of a lossy ping-pong round trip.

  This model intentionally uses only Monae's [probMonad].  There are no
  protocol contracts, no impure interfaces, and no explicit network state:
  each network hop is just a probabilistic coin.
 *)

Module LossyRoundTrip.

Section lossy_round_trip.
  Context {R : realType}.
  Context {M : probMonad R}.

  Inductive packet := Ping | Pong.

  Inductive outcome :=
  | GotPong
  | LostPing
  | LostPong.

  Definition transmit (delivery : {prob R}) (m : packet) : M (option packet) :=
    bcoin delivery >>= fun delivered =>
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

(* ======== will transmit ======== *)
  (* If the delivery probability is 1, [bcoin] always chooses the left branch,
     so transmission immediately returns the packet. *)
  Lemma transmit_certain delivery_packet :
    transmit 1%:i01 delivery_packet = Ret (Some delivery_packet) :> M _.
  Proof.
    by rewrite /transmit /bcoin choice1 bindretf.
  Qed.

  (* A perfect one-shot exchange is just two certain transmissions in a row:
     the client sends [Ping], the server replies [Pong], and the client accepts it. *)
  Lemma ping_pong_once_certain :
    ping_pong_once 1%:i01 = Ret GotPong :> M _.
  Proof.
    by rewrite /ping_pong_once /client_send transmit_certain bindretf /server_reply
               transmit_certain bindretf /client_receive.
  Qed.

  (* Retrying cannot change the result when every attempt succeeds.  The proof
     peels the fuel; the base case is the one-shot lemma, and the step case
     retries only after a failure, which cannot occur. *)
  Lemma ping_pong_retry_certain fuel :
    ping_pong_retry 1%:i01 fuel = Ret GotPong :> M _.
  Proof.
    elim: fuel => [|fuel IH] //=.
    - exact: ping_pong_once_certain.
    by rewrite ping_pong_once_certain bindretf.
  Qed.


  (* ======== may transmit ======== *)

  (* This defintion inverts the loss to a success (for us to read it easier) *)
    Definition delivery_probability (loss : {prob R}) : {prob R} :=
    loss%:num.~%:i01.

  Definition one_attempt_distribution (loss : {prob R}) : M outcome :=
    let delivery := delivery_probability loss in
    (Ret GotPong <| delivery |> Ret LostPong) <| delivery |> Ret LostPing.

  Definition round_trip_success_probability (loss : {prob R}) : {prob R} :=
    let delivery := delivery_probability loss in
    [p_of delivery, delivery].

  Definition one_attempt_failure_distribution (loss : {prob R}) : M outcome :=
    let delivery := delivery_probability loss in
    Ret LostPong <| [q_of delivery, delivery] |> Ret LostPing.

  Definition one_attempt_success_distribution (loss : {prob R}) : M outcome :=
    Ret GotPong
      <| round_trip_success_probability loss |>
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

  (* Expanding the program shows the concrete distribution of one attempt:
     one coin decides whether [Ping] arrives, and, if it does, a second coin
     decides whether [Pong] comes back. *)
  Lemma ping_pong_once_success_probability_shape (loss : {prob R}) :
    ping_pong_once (delivery_probability loss) = one_attempt_distribution loss.
  Proof.
    rewrite /ping_pong_once /client_send /server_reply /client_receive
            /one_attempt_distribution /delivery_probability /transmit /bcoin.
    by rewrite !choice_bindDl !bindretf choice_bindDl !bindretf.
  Qed.

  (* The success probability for a round trip is the product of the two
     independent delivery probabilities: [Ping] must arrive, then [Pong] must
     arrive. *)
  Lemma round_trip_success_probabilityE (loss : {prob R}) :
    (round_trip_success_probability loss)%:num =
    (delivery_probability loss)%:num * (delivery_probability loss)%:num :> R.
  Proof.  by rewrite /round_trip_success_probability p_of_rsE. Qed.

  (* Observing success collapses the three-outcome distribution to a boolean
     coin.  The degenerate delivery cases 0 and 1 are handled separately; in
     the non-degenerate case, associativity and the [p/q] cancellation lemmas
     merge the failure branches into [false]. *)
  Lemma ping_pong_once_success_probability (loss : {prob R}) :
    ping_pong_once_success loss = bcoin (round_trip_success_probability loss).
  Proof.
    rewrite /ping_pong_once_success /observe_success
            ping_pong_once_success_probability_shape
            /one_attempt_distribution /round_trip_success_probability
            /delivery_probability /bcoin.
    set d := loss%:num.~%:i01.
    rewrite choice_bindDl !bindretf choice_bindDl !bindretf.
    have [->/=|d0] := eqVneq d 0%:i01.
    -by rewrite p_of_0s /received_pong
                 (@choice0 R (M : convexMonad R) bool (Ret true) (Ret false))
                 choicemm.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite p_of_1s /received_pong
                 !(@choice1 R (M : convexMonad R) bool (Ret true) (Ret false)).
    rewrite -[Ret false in RHS](choicemm [q_of d, d]).
    rewrite [RHS]choiceA.
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.
    by rewrite (s_of_pqK p1) (r_of_pqK p1 d0) /received_pong.
  Qed.

  (* With zero retry fuel, the retry probability is exactly the one-attempt
     probability, so this is the same product calculation as above. *)
  Lemma retry_success_probabilityE (loss : {prob R}) fuel :
    fuel = O ->
    (retry_success_probability loss fuel)%:num =
    (delivery_probability loss)%:num * (delivery_probability loss)%:num :> R.
  Proof. by move=> ->; rewrite /retry_success_probability round_trip_success_probabilityE. Qed.

  (* The fuelled retry proof is by induction on fuel.  The step separates the
     first attempt from the recursive tail, turns the first attempt into its
     success coin, then uses the induction hypothesis and the choice laws to
     combine "success now" with "success later". *)
  Lemma ping_pong_retry_success_probability (loss : {prob R}) fuel :
    ping_pong_retry_success loss fuel = bcoin (retry_success_probability loss fuel).
  Proof.
    elim: fuel => [|fuel IH] /=.
    - exact: ping_pong_once_success_probability.
    rewrite /ping_pong_retry_success /observe_success /=.
    rewrite bindA.
    transitivity (ping_pong_once (delivery_probability loss) >>=
      (fun x : outcome => Ret (received_pong x) >>=
        (fun ok : bool =>
          if ok then Ret true else ping_pong_retry_success loss fuel))).
    - apply eq_bind => x.
      by case: x; rewrite /received_pong ?bindretf.
    rewrite -bindA.
    change (ping_pong_once (delivery_probability loss) >>=
      (fun x : outcome => Ret (received_pong x))) with
      (ping_pong_once_success loss).
    rewrite ping_pong_once_success_probability.
    rewrite IH /bcoin choice_bindDl !bindretf.
    by rewrite choiceA choicemm.
  Qed.

End lossy_round_trip.

Section concrete_lossy_round_trip.
  Context {R : realType}.

  Definition concrete_ping_pong_once (loss : {prob R}) : acto R outcome :=
    ping_pong_once (M := acto R) (delivery_probability loss).

  Definition concrete_ping_pong_once_success (loss : {prob R}) : acto R bool :=
    ping_pong_once_success (M := acto R) loss.

  Definition concrete_ping_pong_retry_success (loss : {prob R}) (fuel : nat)
    : acto R bool :=
    ping_pong_retry_success (M := acto R) loss fuel.

  Lemma concrete_ping_pong_once_success_probability_shape (loss : {prob R}) :
    concrete_ping_pong_once loss =
    one_attempt_distribution (M := acto R) loss.
  Proof. exact: ping_pong_once_success_probability_shape. Qed.

  Lemma concrete_ping_pong_once_success_probability (loss : {prob R}) :
    concrete_ping_pong_once_success loss =
    bcoin (M := acto R) (round_trip_success_probability loss).
  Proof. exact: ping_pong_once_success_probability. Qed.

  Lemma concrete_ping_pong_retry_success_probability (loss : {prob R}) fuel :
    concrete_ping_pong_retry_success loss fuel =
    bcoin (M := acto R) (retry_success_probability loss fuel).
  Proof. exact: ping_pong_retry_success_probability. Qed.

  Definition concrete_round_trip_success_value (loss : {prob R}) : R :=
    finmap.fun_of_fsfun (FSDist.f (concrete_ping_pong_once_success loss :
      R.-dist (monad_model.choice_of_Type bool))) true.

  Lemma concrete_round_trip_success_valueE (loss : {prob R}) :
    concrete_round_trip_success_value loss =
    (round_trip_success_probability loss)%:num.
  Proof.
    rewrite /concrete_round_trip_success_value
            concrete_ping_pong_once_success_probability /bcoin.
    rewrite fsdist_convE !fsdist1E /=.
    pose ctrue : choice.Choice.sort (monad_model.choice_of_Type bool) := true.
    pose cfalse : choice.Choice.sort (monad_model.choice_of_Type bool) := false.
    rewrite (_ : ctrue \in fset1 ctrue = true); last exact: fset11.
    rewrite (_ : ctrue \in fset1 cfalse = false);
      last by apply/negP => /fset1P.
    by rewrite avgRE mulr1 mulr0 addr0.
  Qed.

  Lemma concrete_round_trip_success_value_pdf (loss : {prob R}) :
    concrete_round_trip_success_value loss =
    (delivery_probability loss)%:num * (delivery_probability loss)%:num :> R.
  Proof.
    by rewrite concrete_round_trip_success_valueE
               round_trip_success_probabilityE.
  Qed.

  Definition concrete_expected_attempts_before_success (loss : {prob R}) : R :=
    (concrete_round_trip_success_value loss)^-1.

  Definition expected_attempts_equation (success expected : R) : Prop :=
    expected = 1 + success.~ * expected.

  Lemma concrete_expected_attempts_before_successE (loss : {prob R}) :
    concrete_expected_attempts_before_success loss =
    ((round_trip_success_probability loss)%:num)^-1.
  Proof.
    by rewrite /concrete_expected_attempts_before_success
               concrete_round_trip_success_valueE.
  Qed.

  Lemma concrete_expected_attempts_before_success_pdf (loss : {prob R}) :
    concrete_expected_attempts_before_success loss =
    ((delivery_probability loss)%:num *
     (delivery_probability loss)%:num)^-1.
  Proof.
    by rewrite concrete_expected_attempts_before_successE
               round_trip_success_probabilityE.
  Qed.

  Lemma concrete_expected_attempts_before_success_yields (loss : {prob R}) :
    (round_trip_success_probability loss)%:num != 0 ->
    expected_attempts_equation
      (round_trip_success_probability loss)%:num
      (concrete_expected_attempts_before_success loss).
  Proof.
    move=> success_nonzero.
    rewrite /expected_attempts_equation concrete_expected_attempts_before_successE.
    set success := (round_trip_success_probability loss)%:num.
    rewrite /onem mulrBl mul1r mulrC mulVf //.
    by rewrite addrC subrK.
  Qed.
End concrete_lossy_round_trip.

End LossyRoundTrip.
