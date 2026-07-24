(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In [FreeSpec.Core.Effect], we have introduced the [effect] type, to
    model the set of primitives an impure computation can use. We also introduce
    [MayProvide], [Provide] and [Distinguish]. They are three type classes which
    allow for manipulating _polymorphic effect composite_.


    In this library, we provide the [freer] monad, defined after the
    <<Program>> monad introduced by the <<operational>> package (see
    <<https://github.com/whitequark/unfork#introduction>>). *)

From FreerDPS Require Import Init.
From mathcomp Require Import all_boot.
From FreerDPS Require Export Effect.

Local Open Scope monae_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

(** We introduce the [freer] monad to describe impure computations, that is
    computations which uses primitives from certain effects. *)

(** * Definition *)

(** The [freer] monad is an inductive datatype with two parameters: the
    effect [F] to be used, and the type [α] of the result of the computation.
    The fact that [freer] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [F]. *)

Inductive freer (F : effect) (α : Type) : Type :=
| pure (x : α) : freer F α
| impure {β} (op : F β) (f : β -> freer F α) : freer F α.

Arguments pure [F α] (x).
Arguments impure [F α β] (op f).

Fixpoint freer_bind (F : effect) {α β} (p : freer F α) (f : α -> freer F β)
    : freer F β :=
  match p with
  | pure x => f x
  | impure Y op g => impure op (fun x => freer_bind (g x) f)
  end.

Declare Scope freer_scope.
Bind Scope freer_scope with freer.
Delimit Scope freer_scope with freer.

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)
(* mode of the freer monad *)
Section freer.
Context (F : effect).
Notation acto := (@freer F).

Let ret : idfun ~~> acto := fun x => @pure F x.

Let bind := fun A B m f => @freer_bind F A B m f.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> T; elim => //b op f ih/=; congr impure; exact/funext. Qed.

Let assoc : BindLaws.associative bind.
Proof. by move=> A B C + f g; elim=>//= *; congr impure; exact/funext. Qed.

#[export]
HB.instance Definition _ := @isMonad_ret_bind.Build acto ret bind
  left_neutral right_neutral assoc.

(** * Defining Freer Computations *)

(** FreeSpec users shall not use the [freer] monad constructors directly.  The
    [pure] function from the [Applicative] typeclass allows for defining pure
    computations which do not depend on any freer primitive.  The [bind]
    function from the [Monad] typeclass allows for seamlessly combine freer
    computations together.

    To complete these two monadic operations, we introduce the [request]
    function, whose purpose is to define an freer computation that uses a given
    primitive [op] from an effect [F], and returns its result.  [request] does
    not parameterize the [freer] monad with [F] directly, but rather with a
    generic effect [Fx].  [Fx] is constrained with the [Provide] notation, so
    that it has to provide at least [F]'s primitives.  *)

End freer.

HB.mixin Record isMonadFreer (F : effect) (M : UU0 -> UU0) of Monad M := {
  request : F ~~> M ;
  denote (N : monad) (l : F ~~> N) : M ~~> N ;
  denote_ret : forall (N : monad) (l : F ~~> N) X (x : X),
    denote N l X (Ret x) = Ret x ;
  denote_bind : forall (N : monad) (l : F ~~> N) X Y m (f : X -> M Y),
    denote N l Y (m >>= f) = denote N l X m >>= (denote N l Y \o f) ;
  denote_request : forall (N : monad) (l : F ~~> N) X (op : F X),
    denote N l X (request X op) = l X op ;
  denote_unique : forall (N : monad) (l : F ~~> N) (denote' : M ~~> N),
      (forall X (x : X), denote' X (ret X x) = Ret x) ->
      (forall X Y (m : M X) (f : X -> M Y), denote' Y (m >>= f) =
         denote' X m >>= (denote' Y \o f)) ->
      (forall X (op : F X), denote' X (request X op) = l X op) ->
    forall X (m : M X), denote' X m = denote N l X m
}.

#[short(type=freerMonad)]
HB.structure Definition MonadFreer (F : effect) :=
  {M of isMonadFreer F M & isMonad M & isFunctor M}.

(** * Monad Instances *)
Module Freer.
Section freer.
Variable F : effect.

Import Monad.

Notation acto := (@freer F).

Definition request_effect : F ~~> acto := fun α op =>
  impure (inj_p op) (@pure _ _).

Definition lifter (M : monad) `(l : F ~~> M) : acto ~~> M :=
  fix aux a (p : acto a) :=
    match p with
    | pure x => Ret x
    | impure Y op f => l _ op >>= fun x => aux a (f x)
    end.

Let lifter_ret (cm : monad) (lifter_effect : F ~~> cm) X (x : X) :
  lifter lifter_effect (ret X x) = @hierarchy.ret cm X x.
Proof. by []. Qed.

Let lifter_bind : forall (cm : monad) (lifter_effect : F ~~> cm) X Y m
    (f : X -> acto Y),
  lifter lifter_effect (m >>= f) =
  lifter lifter_effect m >>= (fun x => lifter lifter_effect (f x)).
Proof.
    move=>cm lifter_effect X Y m f.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf.
    rewrite bindA=>H.
    congr bind.
    exact/boolp.funext/H.
Qed.

Let lifter_trigger (cm : monad) (lifter_effect : F ~~> cm) X (op : F X) :
  lifter lifter_effect (request_effect op) = lifter_effect X op.
Proof. by rewrite /lifter /request_effect/= bindmret. Qed.

Let lifter_unique : forall (cm : monad) (lifter_effect : F ~~> cm)
    (lifter' : acto ~~> cm),
  (forall X (x : X), lifter' X (ret X x) = @hierarchy.ret cm X x) ->
  (forall X Y (m : acto X) (f : X -> acto Y),
    lifter' Y (m >>= f) = lifter' X m >>= (fun x => lifter' Y (f x))) ->
  (forall X (op : F X),
    lifter' X (request_effect op) = lifter_effect X op) ->
  forall X (m : acto X), lifter' X m = lifter lifter_effect m.
Proof.
    move=>cm lifter_effect lifter' dret' dbind' dtrigger' X m.
    rewrite/lifter.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    under [in RHS]eq_bind do rewrite -Hy.
    by rewrite -dtrigger'-dbind'/request_effect.
Qed.

#[export]
HB.instance Definition _ := isMonadFreer.Build F acto
  lifter_ret lifter_bind lifter_trigger lifter_unique.

End freer.
End Freer.
HB.export Freer.

Lemma denote_if : forall (F : effect) (M : freerMonad F) (cm : monad)
   (lifter_effect : F ~~> cm) X (m m' : M X) b,
  denote cm lifter_effect X (if b then m else m') =
  if b then (denote cm lifter_effect X m) else (denote cm lifter_effect X m').
Proof. by move=> ? ? ? ? ? ? ?; case. Qed.

(* example of freer monad using state *)
Module ImpSt.
Section impstate.
Context (F : effect) (S : UU0).

Import Monad.

Definition request_effect {Fx : effect} `{Provide Fx F} {A}
    (op : F A) : freer Fx A :=
  impure (inj_p op) (@pure _ _).

Let iget `{Provide F (STORE S)} : freer F S := request_effect (inj_p Get).
Let iput `{Provide F (STORE S)} (s : S) : freer F () :=
  request_effect (inj_p (Put s)).

(** Note: there have been attempts to turn [request] into a typeclass
    function (to seamlessly use [request] with a [MonadTrans] instance such as
    [state_t]). The reason why it has not been kept into the codebase is that
    the flexibility it gives for writing code has a real impact on the
    verification process. It is simpler to reason about “pure” freer
    computations (that is, not within a monad stack), then wrapping these
    computations thanks to [lift].

    The <<coq-prelude>> provides notations (inspired by the do notation of
    Haskell) to write monadic functions more easily.  These notations live
    inside the [monad_scope]. *)

(** * Lift *)

End impstate.
End ImpSt.

(* HB.export ImpSt. *)

Module FreerFuns.
Definition trigger {Fx : effect} `{Provide Fx F}
    {im : freerMonad Fx} : F ~~> im :=
  fun a op => request a (inj_p op).

Check @trigger.
Arguments trigger {_ _ _ _ _ _} _.

Check (trigger Get).

Definition iget {S} `{Provide F (STORE S)} {im : freerMonad F} : im S :=
  trigger Get.

Definition iput {S} `{Provide F (STORE S)} {im : freerMonad F}
    (s : S) : im unit :=
  trigger (Put s).
End FreerFuns.

HB.export FreerFuns.
