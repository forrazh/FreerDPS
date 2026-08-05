(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)
Local Close Scope nat_scope.
From mathcomp Require Import all_boot.
From mathcomp Require Import boolp.
From monae Require Import hierarchy.
From FreerDPS Require Import Init effect.
From HB Require Import structures.

(* isMonadFreer == interface of the Freer monad *)
(* trigger == TODO *)
(* ptrigger == TODO *)
(* Module FreerFlipDenote == denotation for the freerMonad of the Flip effect *)

Reserved Notation "x <|| p ||> y"
  (at level 40, left associativity, y at next level).
Reserved Notation "a === b" (at level 70).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Declare Scope freer_flip_scope.

Local Open Scope monae_scope.

(** * Definition *)

(** The [freer] monad is an inductive datatype with two parameters: the
    effect [F] to be used, and the type [α] of the result of the computation.
    The fact that [freer] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [F]. *)

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)
(* model of the freer monad *)
Module FreerMonadModel.
Section freer.
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
    generic effect [Fx].  [Fx] is constrained with the [-<] notation, so
    that it has to provide at least [F]'s primitives.  *)

End freer.
End FreerMonadModel.

HB.mixin Record isMonadFreer (F : effect) (M : Type -> Type) of Monad M := {
  trigger : F ~~> M ;
  denote (N : monad) (l : F ~~> N) : M ~~> N ;
  denote_ret : forall (N : monad) (l : F ~~> N) X (x : X),
    denote N l X (Ret x) = Ret x ;
  denote_bind : forall (N : monad) (l : F ~~> N) X Y m (f : X -> M Y),
    denote N l Y (m >>= f) = denote N l X m >>= (denote N l Y \o f) ;
  denote_trigger : forall (N : monad) (l : F ~~> N) X (op : F X),
    denote N l X (trigger X op) = l X op ;
  denote_unique : forall (N : monad) (l : F ~~> N) (denote' : M ~~> N),
      (forall X (x : X), denote' X (ret X x) = Ret x) ->
      (forall X Y (m : M X) (f : X -> M Y), denote' Y (m >>= f) =
         denote' X m >>= (denote' Y \o f)) ->
      (forall X (op : F X), denote' X (trigger X op) = l X op) ->
    forall X (m : M X), denote' X m = denote N l X m
}.

#[short(type=freerMonad)]
HB.structure Definition MonadFreer (F : effect) :=
  {M of isMonadFreer F M & isMonad M & isFunctor M}.

(** * Monad Instances *)
Module Freer.
Section freer.
Variable F : effect.

Import FreerMonadModel.

Notation acto := (@freer F).

Definition trigger_eff : F ~~> acto := fun α op =>
  impure (inj op) (@pure _ _).

Definition dnt (M : monad) (l : F ~~> M) : acto ~~> M :=
  fix aux a (p : acto a) :=
    match p with
    | pure x => Ret x
    | impure Y op f => l _ op >>= fun x => aux a (f x)
    end.

Let dnt_ret (cm : monad) (dnt_eff : F ~~> cm) X (x : X) :
  dnt dnt_eff (ret X x) = @hierarchy.ret cm X x.
Proof. by []. Qed.

Let dnt_bind : forall (cm : monad) (dnt_eff : F ~~> cm) X Y m
    (f : X -> acto Y),
  dnt dnt_eff (m >>= f) =
  dnt dnt_eff m >>= (fun x => dnt dnt_eff (f x)).
Proof.
    move=>cm dnt_eff X Y m f.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf.
    rewrite bindA=>H.
    congr bind.
    exact/boolp.funext/H.
Qed.

Let dnt_trigger (cm : monad) (dnt_eff : F ~~> cm) X (op : F X) :
  dnt dnt_eff (trigger_eff op) = dnt_eff X op.
Proof. by rewrite /dnt /trigger_eff/= bindmret. Qed.

Let dnt_unique : forall (cm : monad) (dnt_eff : F ~~> cm)
    (dnt' : acto ~~> cm),
  (forall X (x : X), dnt' X (ret X x) = @hierarchy.ret cm X x) ->
  (forall X Y (m : acto X) (f : X -> acto Y),
    dnt' Y (m >>= f) = dnt' X m >>= (fun x => dnt' Y (f x))) ->
  (forall X (op : F X),
    dnt' X (trigger_eff op) = dnt_eff X op) ->
  forall X (m : acto X), dnt' X m = dnt dnt_eff m.
Proof.
    move=>cm dnt_eff dnt' dret' dbind' dtrigger' X m.
    rewrite/dnt.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    under [in RHS]eq_bind do rewrite -Hy.
    by rewrite -dtrigger'-dbind'/trigger_eff.
Qed.

#[export]
HB.instance Definition _ := isMonadFreer.Build F acto
  dnt_ret dnt_bind dnt_trigger dnt_unique.

End freer.
End Freer.
HB.export Freer.

HB.mixin Record isMonadFreerInductive
    (F : effect) (M : UU0 -> UU0) of MonadFreer F M := {
  f_ind : forall (P : forall A : UU0, (M A -> Prop)),
    (forall (A : UU0) (x : A), P A (Ret x)) ->
    (forall (A B : UU0) (op : F A) (k : A -> M B),
      (forall x : A, P B (k x)) ->
      P B (trigger A op >>= k)) ->
    forall (A : UU0) (p : M A), P A p
}.

#[short(type=inductiveFreerMonad)]
HB.structure Definition MonadFreerInductive (F : effect) :=
  {M of isMonadFreerInductive F M & isMonadFreer F M &
        isMonad M & isFunctor M}.

Module FreerInductionModel.
Section Model.
Variable F : effect.

Import FreerMonadModel.

Notation acto := (@freer F).

Let freer_induction : forall (P : forall A : UU0, acto A -> Prop),
  (forall (A : UU0) (x : A), P A (Ret x)) ->
  (forall (A B : UU0) (op : F A) (k : A -> acto B),
    (forall x : A, P B (k x)) ->
    P B (trigger A op >>= k)) ->
  forall (A : UU0) (p : acto A), P A p.
Proof.
by move=> P + + A p; elim: p=> //= ??? ih ? H';apply/H'=>?; exact: ih.
Qed.

HB.instance Definition _ :=
  isMonadFreerInductive.Build F acto freer_induction.

End Model.
End FreerInductionModel.
HB.export FreerInductionModel.

Lemma denote_if : forall (F : effect) (M : freerMonad F) (cm : monad)
   (dnt_eff : F ~~> cm) X (m m' : M X) b,
  denote cm dnt_eff X (if b then m else m') =
  if b then (denote cm dnt_eff X m) else (denote cm dnt_eff X m').
Proof. by move=> ? ? ? ? ? ? ?; case. Qed.

Lemma denote_when_trigger (Fx : effect) (M : freerMonad Fx) (cm : monad)
    (l : Fx ~~> cm) (A X : Type) (guard : A -> bool) (op : Fx X) :
  denote cm l unit \o
      (fun x => when (guard x) (trigger X op : M X)) =
    fun x =>
      if guard x then
        l X op >>= (denote cm l unit \o fun=> (skip : M unit))
      else denote cm l unit (skip : M unit).
Proof.
by apply/funext=> x; rewrite functions.compE denote_if;
  case: (guard x)=> //=;
  rewrite denote_bind denote_trigger.
Qed.

Lemma denote_ind {Fx : effect} {M : inductiveFreerMonad Fx}
  : forall (N : monad) (handler : Fx ~~> N)
    (P : forall A : UU0, (N A) -> Prop),
    (forall (A : UU0) (x : A), P A (Ret x)) ->
    (forall (A B : UU0) (h : N A) (k : A -> N B),
      P A h ->
      (forall x : A, P B (k x)) ->
      P B (h >>= k)) ->
    (forall (A : UU0) (op : Fx A), P A (handler A op)) ->
    forall (A : UU0) (p : M A), P A (denote N handler A p).
Proof.
move=> ?? P? Hb *;
apply: (f_ind (fun X => P X \o (denote _ _ X))) => *;
  rewrite functions.compE.
- by rewrite denote_ret.
- by rewrite denote_bind denote_trigger; exact: Hb.
Qed.

(* NB: trigger (TODO: to be renamed trigger) has type
   forall {F : effect} {M : freerMonad F}, F ~~> M
*)

Definition ptrigger {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} : F ~~> M :=
  fun a op => trigger a (inj op).
Arguments ptrigger {_ _ _ _ _} _.

Definition iget {S} {Fx : effect} `{STORE S -< Fx} {M : freerMonad Fx}
    : M S :=
  ptrigger Get.

Definition iput {S} {Fx : effect} `{STORE S -< Fx} {M : freerMonad Fx} (s : S)
    : M unit :=
  ptrigger (Put s).

