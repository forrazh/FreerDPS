(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2024-2027 Univ-Lille *)

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
  fun X op => let: flipe p := op in bcoin p.

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

Lemma denote_choiceA_leftE (handler : Fx ~~> pM)
    (T : UU0) p q (a b c : M T) :
  denote (s := M) pM handler bool (flip p) >>=
    ((denote (s := M) pM handler T) \o
      (fun choice => if choice then a else b <|| q ||> c)) =
  denote (s := M) pM handler bool (flip p) >>=
    (fun choice =>
      if choice then denote (s := M) pM handler T a
      else denote (s := M) pM handler bool (flip q) >>=
        fun nested_choice =>
          denote (s := M) pM handler T
            (if nested_choice then b else c)).
Proof.
by under eq_bind do rewrite compE denote_if denote_freer_choiceE.
Qed.

Lemma denote_choiceA_rightE (handler : Fx ~~> pM)
    (T : UU0) p q (a b c : M T) :
  denote (s := M) pM handler bool (flip [s_of p, q]) >>=
    ((denote (s := M) pM handler T) \o
      (fun choice =>
        if choice then a <|| [r_of p, q] ||> b else c)) =
  denote (s := M) pM handler bool (flip [s_of p, q]) >>=
    (fun choice =>
      if choice then
        denote (s := M) pM handler bool (flip [r_of p, q]) >>=
        fun nested_choice =>
          denote (s := M) pM handler T
            (if nested_choice then a else b)
      else denote (s := M) pM handler T c).
Proof.
by under eq_bind do rewrite compE denote_if denote_freer_choiceE.
Qed.

Lemma denote_choice_bindDlE (handler : Fx ~~> pM)
    (A B : UU0) p (a b : M A) (f : A -> M B) :
  denote pM handler B (a <|| p ||> b >>= f) =
    denote pM handler B ((a >>= f) <|| p ||> (b >>= f)).
Proof.
rewrite denote_bind denote_freer_choiceE
  [in RHS]denote_freer_choiceE.
rewrite -compE bindA; congr bind.
by apply/funext=> -[]; rewrite denote_bind.
Qed.

End denotation.

(** A provided handler can still be built by overriding fallback semantics.
    Unlike the denotation lemmas above, this construction is optional. *)
Section handler_construction.
Context {F Fx : effect} `{F -<? Fx} {N : monad}.

Definition handle_provided
    (handle_effect : F ~~> N) (handle_other : Fx ~~> N) : Fx ~~> N :=
  fun X op =>
    match prj op with
    | Some effect_op => handle_effect X effect_op
    | None => handle_other X op
    end.

End handler_construction.

Section fliphandler_construction.
Context {R : realType} {Fx : effect}
  `{flipprovided : @FlipEff R -< Fx} {pM : probMonad R}.

Definition handle_flip
    (handle_other : Fx ~~> pM) : Fx ~~> pM :=
  handle_provided denote_flipeffect handle_other.

Lemma handle_flipP (handle_other : Fx ~~> pM) :
  handles_flip (handle_flip handle_other).
Proof.
by move=> p; rewrite /handle_flip /handle_provided injK_Some.
Qed.

End fliphandler_construction.


(** The equational structure is generalized in the same way as the syntax.
    Existing exact-effect uses specialize [Fx] to [FlipEff]. *)
(* HB.mixin Record isMonadFreerChoiceEqReas *)
    (* (R : realType) (Fx : effect)
    `{@FlipEff R -< Fx} (M : UU0 -> UU0)
    of MonadFreer Fx M & WBisim M := {
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
HB.structure Definition MonadFreerChoiceEqReas
    (R : realType) (Fx : effect)
    `{H_flip: @FlipEff R -< Fx} :=
  {M of isMonadFreerChoiceEqReas R Fx H_flip M &}.

Section setoid_choiceEqFreerMonad.
Context (R : realType) (Fx : effect)
  `{H_flip: @FlipEff R -< Fx}.
Context {M : choiceEqFreerMonad R Fx H_flip}.

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
move=> x y xy f g fg.
apply: wBisim_trans.
- exact: (bindmwB _ _ _ _ _ xy).
- exact: (bindfwB _ _ _ _ y fg).
Qed.

#[global] Add Parametric Morphism A (p : {prob R}) :
    (freer_choice p) with signature
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
Context {R : realType} {Fx : effect}
  `{H_flip : @FlipEff R -< Fx}.

Notation M := (freer Fx).
Local Notation "x <|| p ||> y" :=
  (@freer_choice R Fx H_flip _ p _ x y).


(* Variant choice_rel :
    forall [X : UU0], M X -> M X -> Prop :=
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

Lemma rel_refl [A : UU0] (x : M A) :
  x ≊ x.
Proof.
  elim : x=> //=.
   constructor. *)


Local Notation "a === b" := (@freer_eq _ _ a b).
Require Import Eqdep.
Ltac ssubst :=
  lazymatch goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep.EqdepTheory.inj_pair2 in H;
      ssubst
  | _ =>
      subst
  end.

(* Goal forall A (a b : M A), a ≊ b -> a === b.
move=> A a b.
case=>[B a' b'||||].
elim: a'=>//=. *)

Lemma c1 A (a b : M A) : (a <|| 1%:i01 ||> b) === a.
Proof . apply: rchoice1. Qed.

Lemma cC A p (a b : M A) :
  (a <|| p ||> b) === (b <|| p%:num.~%:i01 ||> a).
Proof. exact/law_can_bisim/rchoiceC. Qed.

Lemma cmm A p (a : M A) : (a <|| p ||> a) === a.
Proof. exact/law_can_bisim/rchoicemm. Qed.

Lemma cA A p q (a b c : M A) :
  (a <|| p ||> (b <|| q ||> c)) ===
    ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c).
Proof. exact/law_can_bisim/rchoiceA. Qed.

Lemma cbindDl A B p (a b : M A) (f : A -> M B) :
  ((a <|| p ||> b) >>= f) ===
    ((a >>= f) <|| p ||> (b >>= f)).
Proof. exact/law_can_bisim/rchoice_bindDl. Qed.

#[export]
HB.instance Definition _ :=
  isMonadFreerChoiceEqReas.Build R Fx H_flip M
    c1 cC cmm cA cbindDl.

End rel_s.
End RelModel.
 *)
