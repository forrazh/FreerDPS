(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer contract hoare.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Strongest postconditions

    Reference: Aleksandar Nanevski, Greg Morrisett, and Lars Birkedal,
    Hoare type theory, polymorphism and separation.
    Journal of Functional Programming 18(5-6), 865-911, 2008.
    Section 3.2 presents typing rules that generate strongest postconditions.
    https://doi.org/10.1017/S0956796808006953
*)
(* Δ; P ⊢ E ⇒ x:A. Q [E'] *)
(* P ◦ Q = ∃h:heap. [h/mem]P ∧ [h/init]Q *)
Definition SP {S A} (h : hoare S A) (P : S -> Prop)
    (x : A) (s' : S) : Prop :=
  exists s, P s /\ post h s x s'.

Section SPEquations.
Variables (S A B : Type).

Lemma SP_retE (v : A) (P : S -> Prop) :
  SP (hoare_ret v) P =
  (fun x s => P s /\ v = x).
Proof.
apply: eq2_fun=> a s /=.
under eq_exists do rewrite and_mrC andA.
by rewrite ex_andl ex_eqr.
Qed.

Lemma SP_bindE (h : hoare S A) (k : A -> hoare S B)
    (P : S -> Prop) :
  SP (hoare_bind h k) P =
  (fun y s => exists x, SP (k x) (SP h P x) y s).
rewrite /SP /hoare_bind /=.
Proof.
apply: eq2_fun=> a s //=.
under eq_exists do rewrite -ex_andr.
under eq2_exists do rewrite -ex_andr.
under [in RHS]eq2_exists do rewrite -ex_andl.
rewrite 2!ex2C [in RHS]ex2C ex3C;
  apply/eq3_exists=>*.
by rewrite -andA.
Qed.

Lemma SP_ext (h1 h2 : hoare S A) :
  (forall s x s', post h1 s x s' <-> post h2 s x s') ->
  forall P, SP h1 P = SP h2 P.
Proof.
move=>Hpost P.
apply: eq2_fun=> a s; apply: eq_exists=> s'.
by congr and; exact/propext/Hpost.
Qed.

Lemma SP_pre_ext (h : hoare S A) (P1 P2 : S -> Prop) :
  (forall s, P1 s <-> P2 s) ->
  SP h P1 = SP h P2.
Proof.
move=>HP.
apply: eq2_fun=> a s; apply: eq_exists=> s'.
by congr and; exact/propext/HP.
Qed.



Lemma SP_consq (h : hoare S A) (P : S -> Prop)
    (Q : A -> S -> Prop) :
  (forall s, P s -> pre h s) ->
  (forall x s', SP h P x s' -> Q x s') ->
  [h] {{P}} {{Q}} .
Proof.
move=> Hpre Hstrong s Hp.
split=> [|a s' Hpost].
- exact: Hpre.
- by apply: Hstrong; exists s.
Qed.

(** ** Properties of computations (Lemma 4) *)

End SPEquations.
