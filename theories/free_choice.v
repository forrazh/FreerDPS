(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2024–2027 Univ-Lille *)

(******************************************************************************)
(* Probabilistic effect *)
(*                                                                            *)
(* This file features everything that is related to working with a            *)
(* probabilistic effect in FreerDPS.                                          *)
(*                                                                            *)
(* FlipEff == effect for a probabilistic boolean choice *)
(*                                                                            *)
(* References:  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra interval_inference.
From mathcomp Require Import boolp functions reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy proba_lib.
From FreerDPS Require Import init effect freer.

Require Import Morphisms.

Import Order.TTheory Order.Syntax GRing.Theory Num.Theory.

Local Open Scope monae_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

Reserved Notation "x <|| p ||> y"
  (at level 40, left associativity, y at next level).
Reserved Notation "a ≊ b" (at level 70).

(** Effect for a probabilistic Boolean choice. *)
Inductive FlipEff {R : realType} : effect :=
  flipe (p : {prob R}) : FlipEff bool.

(** The exact-effect handler is kept as the canonical denotation of a flip. *)
Section exact_denotation.
Context {R : realType} {pM : probMonad R}.

Definition denote_flipeffect : FlipEff ~~> pM :=
  fun X cmd => let: flipe p := cmd in bcoin p.

Lemma denote_flipeffectE p :
  denote_flipeffect _ (flipe p) = bcoin p.
Proof. by []. Qed.

Lemma denote_flipeffect_injE p :
  denote_flipeffect _ (inj $ flipe p) = bcoin p.
Proof. by []. Qed.

End exact_denotation.

(** The syntax only requires [FlipEff] to be provided by the ambient effect.
    When [Fx] is [FlipEff], the reflexive [Provide] instance recovers the
    original, non-polymorphic interface. *)
Section syntax.
Context {R : realType} {Fx : effect} `{@FlipEff R -< Fx}
  {M : freerMonad Fx}.

Definition flip (p : {prob R}) : M bool := ptrigger $ flipe p.

Definition freer_choice (p : {prob R}) {X} (a b : M X) :=
  flip p >>= fun choice => if choice then a else b.

End syntax.

Notation "x <|| p ||> y" := (freer_choice p x y).

HB.mixin Record isMonadFreerChoiceEqReas (Fx : effect)
    (R : realType) `{@FlipEff R -< Fx} (M : UU0 -> UU0)
    of MonadFreer Fx M & hasWBisim M := {
  freer_choice1 : forall (A : UU0) (a b : M A),
    (a <|| 1%:i01 : {prob R} ||> b) ≈ a;
  freer_choiceC : forall (A : UU0) (p : {prob R}) (a b : M A),
    (a <|| p ||> b) ≈ (b <|| p%:num.~%:i01 ||> a);
  freer_choicemm : forall (A : UU0) (p : {prob R}) (a : M A),
    (a <|| p ||> a) ≈ a;
  freer_choiceA : forall (A : UU0) (p q : {prob R}) (a b c : M A),
    (a <|| p ||> (b <|| q ||> c)) ≈
      ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c);
  freer_choice_bindDl : forall (A B : UU0) (p : {prob R}) (a b : M A)
      (f : A -> M B),
    ((a <|| p ||> b) >>= f) ≈
      ((a >>= f) <|| p ||> (b >>= f))
}.

#[short(type=choiceEqFreerMonad)]
HB.structure Definition MonadFreerChoiceEqReas Fx (R : realType)
    `{flipprovided : @FlipEff R -< Fx} :=
  {M of isMonadFreerChoiceEqReas Fx R flipprovided M &}.

Section setoid_choiceEqFreerMonad.
Context {R : realType} {Fx : effect}
  `{flipprovided : @FlipEff R -< Fx}.
Variable M : choiceEqFreerMonad Fx R flipprovided.

#[global] Add Parametric Relation A : (M A) (@wBisim M A)
  reflexivity proved by (@wBisim_refl M A)
  symmetry proved by (@wBisim_sym M A)
  transitivity proved by (@wBisim_trans M A)
  as wBisim_rel_choiceEqFreerMonad.

#[global] Add Parametric Morphism A B : bind with signature
  (@wBisim M A) ==> (pointwise_relation A (@wBisim M B)) ==>
    (@wBisim M B)
  as bind_mor_choiceEqFreerMonad.
Proof.
move=> a b related f g pointwise_related.
apply: wBisim_trans.
  exact: (bindmwB _ _ _ _ _ related).
exact: (bindfwB _ _ _ _ b pointwise_related).
Qed.

#[global] Add Parametric Morphism A (p : {prob R}) :
    (@freer_choice R Fx flipprovided M p A) with signature
  (@wBisim M A) ==> (@wBisim M A) ==> (@wBisim M A)
  as freer_choice_mor_choiceEqFreerMonad.
Proof.
move=> a a' related_a b b' related_b.
rewrite /freer_choice.
apply: bindfwB=> -[].
  exact: related_a.
exact: related_b.
Qed.

End setoid_choiceEqFreerMonad.

Module ChoiceRelation.
Section relation.
Context {R : realType} {Fx : effect}
  `{flipprovided : @FlipEff R -< Fx}.
Local Notation M := (freer Fx).

(** Equivalence and bind congruence close the five choice laws. *)
Inductive choice_eq : forall [A : UU0], M A -> M A -> Prop :=
| choice_refl A (a : M A) : choice_eq a a
| choice_sym A (a b : M A) : choice_eq a b -> choice_eq b a
| choice_trans A (a b c : M A) :
    choice_eq a b -> choice_eq b c -> choice_eq a c
| choice_bindm A B (f : A -> M B) (a b : M A) :
    choice_eq a b -> choice_eq (a >>= f) (b >>= f)
| choice_bindf A B (f g : A -> M B) (a : M A) :
    (forall x, choice_eq (f x) (g x)) ->
    choice_eq (a >>= f) (a >>= g)
| choice1 A (a b : M A) :
    choice_eq (a <|| 1%:i01 : {prob R} ||> b) a
| choiceC A (p : {prob R}) (a b : M A) :
    choice_eq (a <|| p ||> b) (b <|| p%:num.~%:i01 ||> a)
| choicemm A (p : {prob R}) (a : M A) :
    choice_eq (a <|| p ||> a) a
| choiceA A (p q : {prob R}) (a b c : M A) :
    choice_eq (a <|| p ||> (b <|| q ||> c))
      ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c)
| choice_bindDl A B (p : {prob R}) (a b : M A) (f : A -> M B) :
    choice_eq ((a <|| p ||> b) >>= f)
      ((a >>= f) <|| p ||> (b >>= f)).

#[export] HB.instance Definition _ :=
  @hasWBisim.Build (freer Fx) choice_eq choice_refl choice_sym choice_trans
    choice_bindm choice_bindf.

#[export] HB.instance Definition _ :=
  isMonadFreerChoiceEqReas.Build Fx R flipprovided (freer Fx)
    choice1 choiceC choicemm choiceA choice_bindDl.

End relation.
End ChoiceRelation.
