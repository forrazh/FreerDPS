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

Declare Scope freer_flip_scope.
Local Open Scope monae_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

Reserved Notation "x <|| p ||> y"
  (at level 40, left associativity, y at next level).
Reserved Notation "a ≊ b" (at level 70).


Inductive FlipEff {R : realType} : effect :=
  flip_e (p : {prob R}) : FlipEff bool.

Module FreerFlipDenote.
Section freer_flip.
Context {R : realType} {M : freerMonad (@FlipEff R)} {pM : probMonad R}.
Implicit Type p q r s : {prob R}.

Definition flip p : M bool := ptrigger $ flip_e p.

Definition denote_flip_effect : FlipEff ~~> pM :=
  fun X fx => let: flip_e p := fx in bcoin p.
Lemma denote_flip_effect_pE p : denote_flip_effect _ (flip_e p) = bcoin p.
Proof. by []. Qed.
Lemma denote_flip_effect_inj_pE p : denote_flip_effect _ (inj $ flip_e p) = bcoin p.
Proof. by []. Qed.

Lemma denote_flipE p :
  denote (s := M) pM denote_flip_effect bool (flip p) = bcoin p.
Proof. exact: denote_trigger. Qed.

Definition freer_choice p {X} (a b : M X) :=
  flip p >>= (fun b0 => if b0 then a else b).

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
HB.structure Definition MonadFreerChoiceEqReas Fx (R : realType) `{H: @FlipEff R -< Fx} :=
  {M of isMonadFreerChoiceEqReas Fx R H M &}.

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
  @hasWBisim.Build (freer Fx) choice_eq choice_refl choice_sym choice_trans choice_bindm choice_bindf.

#[export] HB.instance Definition _ :=
  isMonadFreerChoiceEqReas.Build Fx R flipprovided (freer Fx) choice1 choiceC choicemm choiceA choice_bindDl.

End relation.
End ChoiceRelation.

(** Denotation is phrased in terms of a total handler for [Fx].  The only
    semantic fact needed about that handler is its action on injected flips.
    This works for both the exact and provided-effect cases. *)
Section denotation.
Context {R : realType} {Fx : effect}
  `{@FlipEff R -< Fx}
  {M : freerMonad Fx} {pM : probMonad R}.
(* Local Notation "'flip' p" := (@flip R Fx flipprovided M p)
  (at level 10). *)
Local Notation "x <|| p ||> y" := (freer_choice p x y).
Implicit Types p q : {prob R}.
Definition handles_flip (handler : Fx ~~> pM) :=
  forall p, handler _ (inj $ flipe p) = bcoin p.

Lemma denote_flipE (handler : Fx ~~> pM)
    (handler_flip : handles_flip handler) p :
  denote (s := M) pM handler bool (flip p) = bcoin p.
Proof. by rewrite denote_trigger handler_flip. Qed.

Goal forall (handler : Fx ~~> pM) X (p : {prob R}) (a b : M X), denote pM handler X (a <|| p ||> b) = denote (s:=M) pM handler bool (flip p) >>= (fun b' => denote pM handler X (if b' then a else b)).
Proof.
move=>h X p a b.
by rewrite denote_bind; under eq_bind do rewrite compE denote_if.
Qed.

Lemma denote_freer_choiceE (handler : Fx ~~> pM)
    (X : UU0) (p: {prob R}) (a b : M X) :
  denote (s := M) pM handler X (a <|| p ||> b) =
    denote (s := M) pM handler bool (flip p) >>=
      fun choice =>
        denote (s := M) pM handler X (if choice then a else b).
Proof.
by rewrite denote_bind; under eq_bind do rewrite compE denote_if.
Qed.

Lemma denote_choiceA_leftE (T : UU0) p q (a b c : M T) :
  denote (s := M) pM denote_flip_effect bool (flip p) >>=
    ((denote (s := M) pM denote_flip_effect T) \o
      (fun b0 => if b0 then a else b <|| q ||> c)) =
  denote (s := M) pM denote_flip_effect bool (flip p) >>=
    (fun b0 =>
      if b0 then denote (s := M) pM denote_flip_effect T a
      else denote (s := M) pM denote_flip_effect bool (flip q) >>=
        (fun b1 => denote (s := M) pM denote_flip_effect T (if b1 then b else c))).
Proof.
by under eq_bind do rewrite compE denote_if denote_freer_choiceE.
Qed.

Local Open Scope reals_ext_scope.

Lemma denote_choiceA_rightE (T : UU0) p q (a b c : M T) :
  denote (s := M) pM denote_flip_effect bool (flip [s_of p, q]) >>=
    ((denote (s := M) pM denote_flip_effect T) \o
      (fun b0 => if b0 then a <|| [r_of p, q] ||> b else c)) =
  denote (s := M) pM denote_flip_effect bool (flip [s_of p, q]) >>=
    (fun b0 =>
      if b0 then
        denote (s := M) pM denote_flip_effect bool
          (flip [r_of p, q]) >>=
            (fun b1 => denote (s := M) pM denote_flip_effect T (if b1 then a else b))
      else
        denote (s := M) pM denote_flip_effect T c).
Proof.
by under eq_bind do rewrite compE denote_if denote_freer_choiceE.
Qed.

Lemma denote_choice_bindDlE (A B : UU0) p (a b : M A)
  (f : A -> M B) :
  denote pM denote_flip_effect B (a <|| p ||> b >>= f) =
    denote pM denote_flip_effect B ((a >>= f) <|| p ||> (b >>= f)).
Proof.
rewrite denote_bind denote_freer_choiceE [in RHS]denote_freer_choiceE.
rewrite -compE bindA; congr bind.
by apply/funext => -[]; rewrite denote_bind.
Qed.

End freer_flip.
Notation "x <|| p ||> y" := (@freer_choice _ _ p _ x y).
End FreerFlipDenote.

Import FreerFlipDenote.

HB.mixin Record isMonadFreerChoiceEqReas
    (R : realType) (M : UU0 -> UU0) of MonadFreerEqReas (@FlipEff R) M := {
  freer_choice1 : forall (A : UU0) (a b : M A),
    (a <|| 1%:i01 : {prob R} ||> b) ≈ a;
  freer_choiceC : forall (A : UU0) p (a b : M A),
    (a <|| p ||> b) ≈ (b <|| p%:num.~%:i01 ||> a);
  freer_choicemm : forall (A : UU0) p (a : M A),
    (a <|| p ||> a) ≈ a;
  freer_choiceA : forall (A : UU0) p q (a b c : M A),
    (a <|| p ||> (b <|| q ||> c)) ≈
      ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c);
  freer_choice_bindDl : forall (A B : UU0) p (a b : M A)
      (f : A -> M B),
    ((a <|| p ||> b) >>= f) ≈
      ((a >>= f) <|| p ||> (b >>= f))
}.

#[short(type=choiceEqFreerMonad)]
HB.structure Definition MonadFreerChoiceEqReas (R : realType) :=
  {M of isMonadFreerChoiceEqReas R M &}.

Section setoid_choiceEqFreerMonad.
Variables (R : realType) (M : choiceEqFreerMonad R).

#[global] Add Parametric Morphism A (p : {prob R}) :
    (@freer_choice R M p A) with signature
  (@wBisim M A) ==> (@wBisim M A) ==> (@wBisim M A)
  as freer_choice_mor_eqFreerMonad.
Proof.
move=> a a' aa b b' bb.
rewrite /freer_choice.
apply: bindfwB=> -[].
- exact: aa.
- exact: bb.
Qed.

End setoid_choiceEqFreerMonad.

Module RelModel.
Section rel_s.

Context {R : realType}.
Notation M := (freer (@FlipEff R)).

Inductive choice_rel :
    forall [X : UU0], freer (@FlipEff R) X -> freer (@FlipEff R) X -> Prop :=
| rchoice1 : forall [A : UU0] (a b : M A),
    (a <|| 1%:i01 ||> b) ≊ a
| rchoiceC : forall [A : UU0] p (a b : M A),
    (a <|| p ||> b) ≊ (b <|| p%:num.~%:i01 ||> a)
| rchoicemm : forall [A : UU0] p (a : M A),
    (a <|| p ||> a) ≊ a
| rchoiceA : forall [A : UU0] p q (a b c : M A),
    (a <|| p ||> (b <|| q ||> c)) ≊
      ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c)
| rchoice_bindDl : forall [A B : UU0] p (a b : M A)
    (f : A -> M B),
    ((a <|| p ||> b) >>= f) ≊
      ((a >>= f) <|| p ||> (b >>= f))
where "a ≊ b" := (@choice_rel _ a b).

Notation "a === b" := (@freer_eq _ choice_rel _ a b).

Lemma c1 : forall A (a b : M A), (a <|| 1%:i01 ||> b) === a.
Proof. by move=>*; exact/law_can_bisim/rchoice1. Qed.

Lemma cC : forall A p (a b : M A),
  (a <|| p ||> b) === (b <|| p%:num.~%:i01 ||> a).
Proof. by move=>*; exact/law_can_bisim/rchoiceC. Qed.

Lemma cmm : forall A p (a : M A), (a <|| p ||> a) === a.
Proof. by move=>*; exact/law_can_bisim/rchoicemm. Qed.

Lemma cA : forall A p q (a b c : M A),
  (a <|| p ||> (b <|| q ||> c)) ===
    ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c).
Proof. by move=>*; exact/law_can_bisim/rchoiceA. Qed.

Lemma cbindDl : forall A B p (a b : M A) (f : A -> M B),
  ((a <|| p ||> b) >>= f) ===
    ((a >>= f) <|| p ||> (b >>= f)).
Proof. by move=>*; exact/law_can_bisim/rchoice_bindDl. Qed.

#[export]
HB.instance Definition _ := isMonadFreerChoiceEqReas.Build
  R M c1 cC cmm cA cbindDl.
End rel_s.
End RelModel.
