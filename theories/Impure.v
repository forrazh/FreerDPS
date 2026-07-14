(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In [FreeSpec.Core.Interface], we have introduced the [interface] type, to
    model the set of primitives an impure computation can use. We also introduce
    [MayProvide], [Provide] and [Distinguish]. They are three type classes which
    allow for manipulating _polymorphic interface composite_.


    In this library, we provide the [impure] monad, defined after the
    <<Program>> monad introduced by the <<operational>> package (see
    <<https://github.com/whitequark/unfork#introduction>>). *)

From mathcomp Require Import all_boot boolp.
From Stdlib Require Import Program Setoid Morphisms.
From HB Require Import structures.
From monae Require Import preamble hierarchy.
From FreerDPS Require Export Interface.

Local Open Scope monae_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

(** We introduce the [impure] monad to describe impure computations, that is
    computations which uses primitives from certain interfaces. *)

(** * Definition *)

(** The [impure] monad is an inductive datatype with two parameters: the
    interface [i] to be used, and the type [α] of the result of the computation.
    The fact that [impure] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [i]. *)

Inductive freer (i : effect) (α : Type) : Type :=
| pure (x : α) : freer i α
| impure {β} (e : i β) (f : β -> freer i α) : freer i α.

Arguments pure [i α] (x).
Arguments impure [i α β] (e f).

Fixpoint freer_bind (i : effect) {α β} (p : freer i α) (f : α -> freer i β)
    : freer i β :=
  match p with
  | pure x => f x
  | impure Y e g => impure e (fun x => freer_bind (g x) f)
  end.

Declare Scope freer_scope.
Bind Scope freer_scope with freer.
Delimit Scope freer_scope with freer.

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)
(* mode of the freer monad *)
Module Monad.
Section freer.
Context (i : UU0 -> UU0).
Definition acto := @freer i.
Notation FM := acto.

Let ret : idfun ~~> FM := fun x => @pure i x.

Let bind := fun A B m f => @freer_bind i A B m f.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof. by []. Qed.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> T; elim => //b e f ih/=; congr impure; exact/funext. Qed.

Let assoc : BindLaws.associative bind.
Proof. by move=> A B C + f g; elim=>//= *; congr impure; exact/funext. Qed.

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
    primitive [e] from an interface [i], and returns its result.  [request] does
    not parameterize the [freer] monad with [i] directly, but rather with a
    generic interface [ix].  [ix] is constrained with the [Provide] notation, so
    that it has to provide at least [i]'s primitives.  *)

End freer.
End Monad.

(*HB.export FreerModule.*)

HB.mixin Record isMonadFreer (i : effect) (M : UU0 -> UU0) of Monad M := {
  request : i ~~> M ;
  denote (N : monad) (l : i ~~> N) : M ~~> N ;
  denote_ret : forall (N : monad) (l : i ~~> N) X (x : X),
    denote N l X (ret X x) = @ret N X x ;
  denote_bind : forall (N : monad) (l : i ~~> N) X Y m (f : X -> M Y),
    denote N l Y (m >>= f) = denote N l X m >>= (fun x => denote N l Y (f x)) ;
  denote_request : forall (N : monad) (l : i ~~> N) X (fx : i X),
    denote N l X (request X fx) = l X fx ;
  denote_unique : forall (N : monad) (l : i ~~> N) (denote' : M ~~> N),
      (forall X (x : X), denote' X (ret X x) = @ret N X x) ->
      (forall X Y (m : M X) (f : X -> M Y), denote' Y (m >>= f) =
         (denote' X m) >>= (fun x => denote' Y (f x))) ->
      (forall X (fx : i X), (denote' X (request X fx)) = l X fx) ->
    forall X (m : M X), denote' X m = denote N l X m
}.

#[short(type=freerMonad)]
HB.structure Definition MonadFreer (i : interface) :=
  {M of isMonadFreer i M & isMonad M & isFunctor M}.

(** * Monad Instances *)
Module Freer.
Section freer.
Variable i : interface.

Import Monad.

Local Notation M := (acto i).

Definition requesti : i ~~> acto i := fun α e => 
  impure (inj_p e) (@pure _ _).

Definition lifter (M : monad) `(l : i ~~> M) : acto i ~~> M :=
  fix aux a (p : acto i a) :=
    match p with
    | pure x => Ret x
    | impure Y e f => l _ e >>= fun x => aux a (f x)
    end.

Let lifter_ret : forall (cm : monad) (lifter_effect : i ~~> cm) X (x : X),
        lifter lifter_effect (ret X x) = @hierarchy.ret cm X x.
Proof.
  rewrite/=/lifter.
    by [].
Qed.


Let lifter_bind : forall (cm : monad) (lifter_effect : i ~~> cm) X Y m (f : X -> M Y), 
        lifter lifter_effect (m >>= f) = ( lifter lifter_effect m) >>= (fun x => lifter lifter_effect (f x)) .
Proof.
    move=>cm lifter_effect X Y m f.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf. 
    rewrite bindA=>H.
    congr bind.
    exact/boolp.funext/H.
Qed.

Let lifter_trigger (cm : monad) (lifter_effect : i ~~> cm) X (fx : i X) :
  lifter lifter_effect (requesti fx) = lifter_effect X fx.
Proof. by rewrite /lifter /requesti/= bindmret. Qed.

Let lifter_unique : forall (cm : monad) (lifter_effect : i ~~> cm) (lifter' : M ~~> cm),
            (forall X (x : X), lifter' X (ret X x) = @hierarchy.ret cm X x) ->
            (forall X Y (m : M X) (f : X -> M Y), lifter' Y (m >>= f) = (lifter' X m) >>= (fun x => lifter' Y (f x))) ->
            (forall X (fx : i X), (lifter' X (requesti fx)) = lifter_effect X fx) ->
        forall X (m : M X), lifter' X m = lifter lifter_effect m.
Proof.
    move=>cm lifter_effect lifter' dret' dbind' dtrigger' X m.
    rewrite/lifter.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    under [in RHS]eq_bind do rewrite -Hy.
    by rewrite -dtrigger'-dbind'/requesti.
Qed.

HB.instance Definition _ := isMonadFreer.Build i M
  lifter_ret lifter_bind lifter_trigger lifter_unique.

End freer.
End Freer.

Lemma denote_if : forall (i : effect) (M : freerMonad i) (cm : monad)
   (lifter_effect : i ~~> cm) X (m m' : M X) b,
  denote cm lifter_effect X (if b then m else m') =
  if b then (denote cm lifter_effect X m) else (denote cm lifter_effect X m').
Proof. by move=> ? ? ? ? ? ? ?; case. Qed.

(* example of freer monad using state *)
Module ImpSt.
Section impstate.
Context (i : effect) (S : UU0).

Import Monad.

Definition requestis `{Provide ix i} {A} (e : i A): acto ix A :=
  impure (inj_p e) (@pure _ _).

  Let iget `{Provide i (STORE S)} : acto i S:=requestis (inj_p Get).
  Let iput `{Provide i (STORE S)} (s : S) : acto i ():=requestis (inj_p (Put s)).

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
Definition trigger  `{Provide ix i} {im : freerMonad ix} : ix ~~> im := fun a e => request a (inj_p e). 
Definition iget {S} `{Provide i (STORE S)} {im : freerMonad i} : im S:= trigger (inj_p Get).
Definition iput {S} `{Provide i (STORE S)} {im : freerMonad i} (s : S) : im unit:= trigger (inj_p (Put s)).
End FreerFuns.

(*HB.export FreerFuns.*)
