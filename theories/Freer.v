(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In [FreeSpec.Core.Effect], we have introduced the [effect] type, to
    model the set of primitives an impure computation can use. We also introduce
    [MayProvide], [Provide] and [Distinguish]. They are three type classes which
    allow for manipulating _polymorphic effect composite_.


    In this library, we provide the [impure] monad, defined after the
    <<Program>> monad introduced by the <<operational>> package (see
    <<https://github.com/whitequark/unfork#introduction>>). *)

From FreerDPS Require Import Init.
From mathcomp Require Import ssrfun.
From FreerDPS Require Export Effect.

Local Open Scope monae_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

(** We introduce the [impure] monad to describe impure computations, that is
    computations which uses primitives from certain effects. *)

(** * Definition *)

(** The [impure] monad is an inductive datatype with two parameters: the
    effect [F] to be used, and the type [α] of the result of the computation.
    The fact that [impure] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [F]. *)

Inductive freer (F : effect) (α : Type) : Type :=
| local (x : α) : freer F α
| request_then {β} (e : F β) (f : β -> freer F α) : freer F α.

#[deprecated(note="Name will change to `freer`.")]
Notation impure := freer (only parsing).

Arguments local [F α] (x).
Arguments request_then [F α β] (e f).

Register freer as freespec.core.impure.type.
Register local as freespec.core.impure.local.
Register request_then as freespec.core.impure.request_then.

Declare Scope impure_scope.
Bind Scope impure_scope with freer.
Delimit Scope impure_scope with impure.

HB.mixin Record isMonadImpure (F : effect) (M : UU0 -> UU0) of Monad M := {
    request : F ~~> M ;
    impure_lift (N : monad) (l : F ~~> N) : M ~~> N ;
    impure_lift_ret : forall (N : monad) (l : F ~~> N) X (x : X),
        impure_lift N l X (ret X x) = @ret N X x;
    impure_lift_bind : forall (N : monad) (l : F ~~> N) X Y m
        (f : X -> M Y),
        impure_lift N l Y (m >>= f) = (impure_lift N l X m) >>= (fun x => impure_lift N l Y (f x)) ;
    impure_lift_request : forall (N : monad) (l : F ~~> N) X (fx : F X),
        impure_lift N l X (request X fx) = l X fx;
    impure_lift_unique : forall (N : monad) (l : F ~~> N) (impure_lift' : M ~~> N),
            (forall X (x : X), impure_lift' X (ret X x) = @ret N X x) ->
            (forall X Y (m : M X) (f : X -> M Y), impure_lift' Y (m >>= f) = (impure_lift' X m) >>= (fun x => impure_lift' Y (f x))) ->
            (forall X (fx : F X), (impure_lift' X (request X fx)) = l X fx) ->
        forall X (m : M X), impure_lift' X m = impure_lift N l X m
}.


#[short(type=impureMonad)]
HB.structure Definition MonadImpure (F : effect) :=
  {M of isMonadImpure F M & isMonad M & isFunctor M}.

(** * Monad Instances *)

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)
Module ImpureModule.
Section freer.

Variable F : UU0 -> UU0.
Definition acto := fun X => @impure F X.
Notation FM := acto.

Definition impure_pure {α} (x : α) : impure F α := local x.

Let ret : idfun ~~> FM := fun _ => impure_pure. 

Fixpoint impure_bind {α β} (p : impure F α) (f : α -> impure F β) : impure F β :=
  match p with
  | local x => f x
  | request_then Y e g => request_then e (fun x => impure_bind (g x) f)
  end.

Let bind := fun A B m f => @impure_bind A B m f.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
     by [].
Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
    move=>/=A.
    elim=>[x|Y fy k IHm]//=.
    congr request_then.
    exact/boolp.funext=>y.
Qed.

Let assoc : BindLaws.associative bind.
Proof.
    move=>/=A B C m f g.
    elim:m=>//=Y fy k IHm.
    congr request_then.
    exact/boolp.funext=>y.
Qed.

HB.instance Definition _ := @isMonad_ret_bind.Build acto ret bind left_neutral right_neutral assoc.

(** * Defining Impure Computations *)

(** FreeSpec users shall not use the [impure] monad constructors directly.  The
    [pure] function from the [Applicative] typeclass allows for defining pure
    computations which do not depend on any impure primitive.  The [bind]
    function from the [Monad] typeclass allows for seamlessly combine impure
    computations together.

    To complete these two monadic operations, we introduce the [request]
    function, whose purpose is to define an impure computation that uses a given
    primitive [e] from an effect [F], and returns its result.  [request] does
    not parameterize the [impure] monad with [F] directly, but rather with a
    generic effect [Fx].  [Fx] is constrained with the [Provide] notation, so
    that it has to provide at least [F]'s primitives.  *)

End freer.
End ImpureModule.

HB.export ImpureModule.

Module Impure.
Section freer.

Variable F : effect.

Local Notation M := (acto F).

Definition request_effect : F ~~> acto F := fun α e =>
  request_then (inj_p e) (fun x => local x).

Definition lifter (M : monad) `(l : F ~~> M) : acto F ~~> M :=
  fix aux a (p : acto F a) :=
    match p with
    | local x => Ret x
    | request_then Y e f => l _ e >>= fun x => aux a (f x)
    end.

Let lifter_ret : forall (cm : monad) (lifter_effect : F ~~> cm) X (x : X),
        lifter lifter_effect (ret X x) = @hierarchy.ret cm X x.
Proof.
  rewrite/=/lifter.
    by [].
Qed.


Let lifter_bind : forall (cm : monad) (lifter_effect : F ~~> cm) X Y m
    (f : X -> M Y),
        lifter lifter_effect (m >>= f) = ( lifter lifter_effect m) >>= (fun x => lifter lifter_effect (f x)) .
Proof.
    move=>cm lifter_effect X Y m f.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf. 
    rewrite bindA=>H.
    congr bind.
    exact/boolp.funext/H.
Qed.

Let lifter_trigger : forall (cm : monad) (lifter_effect : F ~~> cm)
    X (fx : F X),
        lifter lifter_effect (request_effect fx) = lifter_effect X fx.
Proof.
    move=>cm lifter_effect X fx.
    by rewrite /lifter /request_effect /= bindmret.
Qed.

Let lifter_unique : forall (cm : monad) (lifter_effect : F ~~> cm) (lifter' : M ~~> cm),
            (forall X (x : X), lifter' X (ret X x) = @hierarchy.ret cm X x) ->
            (forall X Y (m : M X) (f : X -> M Y), lifter' Y (m >>= f) = (lifter' X m) >>= (fun x => lifter' Y (f x))) ->
            (forall X (fx : F X),
              lifter' X (request_effect fx) = lifter_effect X fx) ->
        forall X (m : M X), lifter' X m = lifter lifter_effect m.
Proof.
    move=>cm lifter_effect lifter' dret' dbind' dtrigger' X m.
    rewrite/lifter.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    under [in RHS]eq_bind do rewrite -Hy.
    by rewrite -dtrigger' -dbind' /request_effect.
Qed.

HB.instance Definition _ := isMonadImpure.Build F M
  lifter_ret 
  lifter_bind 
  lifter_trigger
  lifter_unique.

End freer.
End Impure.
HB.export Impure.

Lemma impure_lift_if : forall (F : effect) (M : impureMonad F) (cm : monad)
    (lifter_effect : F ~~> cm) X (m m' : M X) b,
        impure_lift cm lifter_effect X (if b then m else m') = if b then ( impure_lift cm lifter_effect X m) else ( impure_lift cm lifter_effect X m').
Proof.
    by move=>? ? ? ? ? ? ?; case.
Qed.
HB.export impure_lift_if.

Module ImpSt.
  Section impstate.
        Variable F : effect.
        Variable S : UU0.
Definition request_effect `{Provide Fx F} {A} (e : F A) : acto Fx A :=
  request_then (inj_p e) (fun x => local x).

  Let iget `{Provide F (STORE S)} : acto F S :=
    request_effect (inj_p Get).
  Let iput `{Provide F (STORE S)} (s : S) : acto F () :=
    request_effect (inj_p (Put s)).

(** Note: there have been attempts to turn [request] into a typeclass
    function (to seamlessly use [request] with a [MonadTrans] instance such as
    [state_t]). The reason why it has not been kept into the codebase is that
    the flexibility it gives for writing code has a real impact on the
    verification process. It is simpler to reason about “pure” impure
    computations (that is, not within a monad stack), then wrapping these
    computations thanks to [lift].

    The <<coq-prelude>> provides notations (inspired by the do notation of
    Haskell) to write monadic functions more easily.  These notations live
    inside the [monad_scope]. *)

(** * Lift *)

  End impstate.
End ImpSt.

(* HB.export ImpSt. *)

Module ImpureFuns.
Definition trigger `{Provide Fx F} {im : impureMonad Fx} : Fx ~~> im :=
  fun a e => request a (inj_p e).
Definition iget {S} `{Provide F (STORE S)} {im : impureMonad F} : im S:= trigger (inj_p Get).
Definition iput {S} `{Provide F (STORE S)} {im : impureMonad F} (s : S) : im unit:= trigger (inj_p (Put s)).
End ImpureFuns.

HB.export ImpureFuns.
