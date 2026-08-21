(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)
Local Close Scope nat_scope.
From mathcomp Require Import all_boot all_order.
From mathcomp Require Import boolp functions.
From monae Require Import hierarchy.
From FreerDPS Require Import init effect.
From HB Require Import structures.

Require Import Morphisms.

(* isMonadFreer == interface of the Freer monad *)
(* trigger == TODO *)
(* ptrigger == TODO *)
(* Module FreerFlipDenote == denotation for the freerMonad of the Flip effect *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(** * Definition *)

(** The [freer] monad is an inductive datatype with two parameters: the
    effect [F] to be used, and the type [A] of the result of the computation.
    The fact that [freer] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [F]. *)

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)
(* model of the freer monad *)
Module FreerMonadModel.
Section freer.
Inductive freer (F : effect) (A : Type) :=
| pure (x : A) : freer F A
| impure {B} (op : F B) (f : B -> freer F A) : freer F A.

Arguments pure [F A] (x).
Arguments impure [F A B] (op f).

Fixpoint freer_bind (F : effect) {A B} (p : freer F A) (f : A -> freer F B)
    : freer F B :=
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
HB.export FreerMonadModel.

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

Definition trigger_effect : F ~~> acto := fun A op =>
  impure (inj op) (@pure _ _).

Definition dnt (M : monad) (l : F ~~> M) : acto ~~> M :=
  fix aux a (p : acto a) :=
    match p with
    | pure x => Ret x
    | impure Y op f => l _ op >>= fun x => aux a (f x)
    end.

Let dnt_ret (cm : monad) (dnt_effect : F ~~> cm) X (x : X) :
  dnt dnt_effect (ret X x) = @hierarchy.ret cm X x.
Proof. by []. Qed.

Let dnt_bind : forall (cm : monad) (dnt_effect : F ~~> cm) X Y m
    (f : X -> acto Y),
  dnt dnt_effect (m >>= f) =
  dnt dnt_effect m >>= (fun x => dnt dnt_effect (f x)).
Proof.
    move=>cm dnt_effect X Y m f.
    elim:m=>[x | Z fz k]/=.
    - by rewrite !bindretf.
    rewrite bindA=>H.
    congr bind.
    exact/boolp.funext/H.
Qed.

Let dnt_trigger (cm : monad) (dnt_effect : F ~~> cm) X (op : F X) :
  dnt dnt_effect (trigger_effect op) = dnt_effect X op.
Proof. by rewrite /dnt /trigger_effect/= bindmret. Qed.

Let dnt_unique : forall (cm : monad) (dnt_effect : F ~~> cm)
    (dnt' : acto ~~> cm),
  (forall X (x : X), dnt' X (ret X x) = @hierarchy.ret cm X x) ->
  (forall X Y (m : acto X) (f : X -> acto Y),
    dnt' Y (m >>= f) = dnt' X m >>= (fun x => dnt' Y (f x))) ->
  (forall X (op : F X),
    dnt' X (trigger_effect op) = dnt_effect X op) ->
  forall X (m : acto X), dnt' X m = dnt dnt_effect m.
Proof.
    move=>cm dnt_effect dnt' dret' dbind' dtrigger' X m.
    rewrite/dnt.
    elim:m=>[x| Y fy k Hy]/=.
    - exact/dret'.
    under [in RHS]eq_bind do rewrite -Hy.
    by rewrite -dtrigger'-dbind'/trigger_effect.
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
   (dnt_effect : F ~~> cm) X (m m' : M X) b,
  denote cm dnt_effect X (if b then m else m') =
  if b then (denote cm dnt_effect X m) else (denote cm dnt_effect X m').
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
by apply/funext=> x; rewrite compE denote_if;
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
  rewrite compE.
- by rewrite denote_ret.
- by rewrite denote_bind denote_trigger; exact: Hb.
Qed.

Definition ptrigger {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} : F ~~> M :=
  fun a op => trigger a (inj op).
Arguments ptrigger {_ _ _ _ _} _.

Definition iget {S} {Fx : effect} `{STORE S -< Fx} {M : freerMonad Fx}
    : M S :=
  ptrigger Get.

Definition iput {S} {Fx : effect} `{STORE S -< Fx} {M : freerMonad Fx} (s : S)
    : M unit :=
  ptrigger (Put s).

Definition freer_rel (F : effect) {M : freerMonad F} :=
  forall A, M A -> M A -> Prop.
(*
Definition law_sound [F : effect] [M : freerMonad F]
  (r : freer_rel) (N : monad) (h : F ~~> N) :=
forall A (m n : M A),
  r A m n ->
  denote N h A m = denote N h A n. *)

Module FMwBi.
Section fm_eq_s.

Import FreerMonadModel.
Variable F : effect.
Notation acto := (@freer F).
Variable r : @freer_rel F acto.

Inductive freer_eq [A : UU0] : acto A -> acto A -> Prop :=
| pure_eq x :
    pure _ x === pure _ x
| impure_eq B (op : F B) (f g : B -> acto A) :
    (forall x, f x === g x) ->
    impure op f === impure op g
where "a === b" := (freer_eq a b).

Lemma den_imp [N : monad] [A B : UU0] (h : F ~~> N) op f :
  denote N h A (impure op f) = h B op >>= (fun x => denote N h A (f x)).
Proof. by []. Qed.
(* Lemma freer_eq_sound N h :
  law_sound r h ->
  forall A m n,
    freer_eq m n ->
    denote N h A m = denote N h A n.
Proof.
move=> rh A m n mn.
apply: rh.
by case: mn. *)
(* . /[apply].

 h + r.
by move=> + A m n [??]=> /[swap] /[apply] ->.
Qed. *)
(* Qed. *)
Lemma rel_refl [A : UU0] (x : acto A) :
  x === x.
Proof. by elim: x=> [| B op f]/=; constructor. Qed.

Lemma rel_sym [A : UU0] (x y : acto A) :
  x === y -> y === x.
Proof. by elim; constructor. Qed.

Require Import Eqdep.
Ltac ssubst :=
  lazymatch goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H;
      ssubst
  | _ =>
      subst
  end.

Lemma rel_trans [A : UU0] (x y z : acto A) :
  x === y ->
  y === z ->
  x === z.
Proof.
move: x z.
elim: y=>[a | B op f ih] x z xy xz;
   inversion xy; subst;
   inversion xz; ssubst.
- exact: pure_eq.
- by apply: impure_eq=> b; exact: (ih b).
Qed.

Add Parametric Relation {A : UU0} : (acto A) (@freer_eq A)
  reflexivity proved by (@rel_refl A)
  symmetry proved by (@rel_sym A)
  transitivity proved by (@rel_trans A)
  as wBisims_rel.
Hint Extern 0 (freer_eq _ _) => setoid_reflexivity : core.

Lemma eq_bindmwB [A B : UU0] (f : A -> acto B) (d1 d2 : acto A) :
  d1 === d2 -> (d1 >>= f) === (d2 >>= f).
Proof. by elim=>// C op g g' Hgg ih; exact/impure_eq/ih. Qed.

Lemma eq_bindfwB
    [A B : UU0] (f g : A -> acto B) (d : acto A) :
  (forall a, (f a) === (g a)) ->
  (d >>= f) === (d >>= g).
Proof. by move=>*; elim: d=> //c op h ih; exact/impure_eq/ih. Qed.

#[export]
HB.instance Definition _ := hasWBisim.Build acto rel_refl rel_sym rel_trans eq_bindmwB eq_bindfwB.

End fm_eq_s.
Arguments freer_eq {_ _} a b.
Notation "a === b" := (freer_eq a b).
End FMwBi.
HB.export FMwBi.


(* HB.mixin Record isMonadFreerEqReas (F : effect) (M : UU0 -> UU0)
  of MonadFreer F M & hasWBisim M := {
  law : freer_rel;
  law_can_bisim : forall A (x y : M A), law A x y -> x ≈ y ;
  (* bisim_denotes : forall A cm h (x y : M A), law_sound law h -> x ≈ y ->
    denote cm h A x = denote cm h A y ; *)
}. *)

(* #[short(type=eqFreerMonad)]
HB.structure Definition MonadFreerEqReas (F : effect) :=
  {M of isMonadFreerEqReas F M &}. *)

(* Section setoid_eqFreerMonad.
Variables (F : effect) (M : eqFreerMonad F).

#[global] Add Parametric Relation A : (M A) (@wBisim M A)
  reflexivity proved by (@wBisim_refl M A)
  symmetry proved by (@wBisim_sym M A)
  transitivity proved by (@wBisim_trans M A)
  as wBisim_rel_eqFreerMonad.

#[global] Add Parametric Morphism A B : bind with signature
  (@wBisim M A) ==> (pointwise_relation A (@wBisim M B)) ==>
    (@wBisim M B)
  as bind_mor_eqFreerMonad.
Proof.
move=> x y xy f g fg.
apply: wBisim_trans.
- exact: (bindmwB _ _ _ _ _ xy).
- exact: (bindfwB _ _ _ _ y fg).
Qed.

End setoid_eqFreerMonad. *)

Module FMEq.
Section fm_sec.

Import FreerMonadModel.
Variable F : effect.
Notation acto := (@freer F).
Variable law : @freer_rel F acto.

Notation "a === b" := (@freer_eq F law _ a b).

(* Lemma law_feq : forall A (x y : acto A), law x y -> x === y.
Proof.
by move=>*; apply: law_eq=>??; apply.
Qed. *)

(* Lemma feq_den  A cm h (x y : acto A) :
  law_sound law h -> x === y -> denote cm h A x = denote cm h A y.
Proof.
by move=> Hlaw [m n]; apply.
Qed. *)

(* #[export]
HB.instance Definition _ := isMonadFreerEqReas.Build F acto law_feq. *)

End fm_sec.
End FMEq.
HB.export FMEq.
