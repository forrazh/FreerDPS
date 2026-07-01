From mathcomp Require Import ssreflect ssrbool ssrnum ssralg reals
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib.
From FreerDPS Require Import Core.
From EG.ping Require Import lossy_round_trip_impure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

(**
  A deterministic FreeSpec semantics for [prob_interface].

  The [semantics] type from [Semantics.v] returns a concrete result and an
  updated semantics.  For a probabilistic interface, this means one run is
  driven by an oracle of already-sampled Boolean choices.
 *)

Module LossyRoundTripImpureSemantics.

Module LRT := LossyRoundTripImpure.

Section prob_semantics.
  Context {R : realType}.

  CoFixpoint prob_semantics_from (oracle : nat -> bool) (n : nat)
    : semantics (@prob_interface R) :=
    mk_semantics (fun X (e : @prob_interface R X) =>
      match e in prob_interface X return X * semantics (@prob_interface R) with
      | CanWork _ => (oracle n, prob_semantics_from oracle (S n))
      end).

  Definition prob_semantics (oracle : nat -> bool)
    : semantics (@prob_interface R) :=
    prob_semantics_from oracle 0.

  Definition always (b : bool) : nat -> bool := fun _ => b.

  Definition prob_step (sem : semantics (@prob_interface R))
    : forall X, @prob_interface R X -> X -> semantics (@prob_interface R) :=
    fun X e _ => exec_effect sem e.

  Definition prob_callee (sem : semantics (@prob_interface R))
    : forall X, @prob_interface R X -> X -> Prop :=
    fun X e x => eval_effect sem e = x.

  Definition prob_specs
    : contract (@prob_interface R) (semantics (@prob_interface R)) :=
    make_contract prob_step no_caller_obligation prob_callee.

  Local Notation prob_impure :=
    (ImpureModule_acto__canonical__Impure_MonadImpure (@prob_interface R)).

  Lemma prob_specs_pre X
      (p : impure (@prob_interface R) X)
      (sem : semantics (@prob_interface R)) :
    pre (to_hoare (im:=prob_impure) prob_specs p) sem.
  Proof.
    move: sem.
    elim: p => [x|Y e k IH] sem /=.
    - done.
    split.
    - constructor.
    move=> x sem' _.
    exact: IH.
  Qed.

  Lemma transmit_pre (sem : semantics (@prob_interface R))
      delivery packet :
    pre (to_hoare (im:=prob_impure) prob_specs
      (LRT.transmit (im:=prob_impure) delivery packet)) sem.
  Proof. exact: prob_specs_pre. Qed.

  Lemma ping_pong_once_pre (sem : semantics (@prob_interface R))
      delivery :
    pre (to_hoare (im:=prob_impure) prob_specs
      (LRT.ping_pong_once (im:=prob_impure) delivery)) sem.
  Proof. exact: prob_specs_pre. Qed.

  Lemma eval_transmit oracle n delivery packet :
    eval_impure (prob_semantics_from oracle n)
      (LRT.transmit (im:=prob_impure) delivery packet)
    = if oracle n then Some packet else None.
  Proof.
    by rewrite /eval_impure /run_impure /to_state /LRT.transmit /=.
  Qed.

  Lemma run_transmit oracle n delivery packet :
    run_impure (prob_semantics_from oracle n)
      (LRT.transmit (im:=prob_impure) delivery packet)
    =
    (if oracle n then Some packet else None,
     prob_semantics_from oracle (S n)).
  Proof.
    by rewrite /run_impure /to_state /LRT.transmit /=.
  Qed.

  Lemma eval_ping_pong_once oracle n delivery :
    eval_impure (prob_semantics_from oracle n)
      (LRT.ping_pong_once (im:=prob_impure) delivery)
    =
    if oracle n
    then if oracle (S n) then LRT.GotPong else LRT.LostPong
    else LRT.LostPing.
  Proof.
    rewrite /eval_impure /run_impure /to_state /LRT.ping_pong_once
            /LRT.client_send.
    rewrite impure_lift_bind /LRT.transmit
            impure_lift_bind impure_lift_request.
    rewrite /interface_to_state /bind /=.
    case: (oracle n) => /=.
    - rewrite /impure_lift /Impure.lifter /bind /=.
      rewrite /LRT.client_receive /Impure.lifter /bind /=.
      case: (oracle (S n)) => /=; reflexivity.
    done.
  Qed.

  Lemma run_ping_pong_once oracle n delivery :
    run_impure (prob_semantics_from oracle n)
      (LRT.ping_pong_once (im:=prob_impure) delivery)
    =
    (if oracle n
     then if oracle (S n) then LRT.GotPong else LRT.LostPong
     else LRT.LostPing,
     if oracle n
     then prob_semantics_from oracle (S (S n))
     else prob_semantics_from oracle (S n)).
  Proof.
    rewrite /run_impure /to_state /LRT.ping_pong_once
            /LRT.client_send.
    rewrite impure_lift_bind /LRT.transmit
            impure_lift_bind impure_lift_request.
    rewrite /interface_to_state /bind /=.
    case: (oracle n) => /=.
    - rewrite /impure_lift /Impure.lifter /bind /=.
      rewrite /LRT.client_receive /Impure.lifter /bind /=.
      case: (oracle (S n)) => /=; reflexivity.
    done.
  Qed.

  Lemma all_success_ping_pong_once delivery :
    eval_impure (prob_semantics (always true))
      (LRT.ping_pong_once (im:=prob_impure) delivery)
    = LRT.GotPong.
  Proof. by rewrite eval_ping_pong_once. Qed.

  Lemma all_loss_ping_pong_once delivery :
    eval_impure (prob_semantics (always false))
      (LRT.ping_pong_once (im:=prob_impure) delivery)
    = LRT.LostPing.
  Proof. by rewrite eval_ping_pong_once. Qed.

End prob_semantics.

End LossyRoundTripImpureSemantics.
