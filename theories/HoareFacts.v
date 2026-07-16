(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From mathcomp Require Import ssreflect.
From FreerDPS Require Import Interface Impure Contract Hoare.
From monae Require Import preamble hierarchy.
Generalizable All Variables.

Local Open Scope monae_scope.

(** * Hoare Interpretation Views *)

Section GenericHoareSection.
Context `{MayProvide ix i} {im : freerMonad ix} `(c : contract i Ω).

Lemma interface_to_hoare_preE `(e : ix a) (ω : Ω) :
  pre (interface_to_hoare c e) ω <-> gen_caller_obligation c ω e.
Proof. by split. Qed.

Lemma interface_to_hoare_postE `(e : ix a) (ω : Ω) (x : a) (ω' : Ω) :
  post (interface_to_hoare c e) ω x ω' <->
  ω' = gen_witness_update c ω e x /\
  gen_callee_obligation c ω e x.
Proof. by split. Qed.

Lemma interface_to_hoare_postI `(e : ix a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω e x ->
  post (interface_to_hoare c e) ω x (gen_witness_update c ω e x).
Proof. by move=> step; split. Qed.

Lemma to_hoare_requestE `(e : ix a) :
  to_hoare (im:=im) c (request a e) = interface_to_hoare c e.
Proof. exact: denote_request. Qed.

Lemma to_hoare_request_preE `(e : ix a) (ω : Ω) :
  pre (to_hoare (im:=im) c (request a e)) ω <->
  gen_caller_obligation c ω e.
Proof. by rewrite to_hoare_requestE interface_to_hoare_preE. Qed.

Lemma to_hoare_request_postE `(e : ix a) (ω : Ω) (x : a) (ω' : Ω) :
  post (to_hoare (im:=im) c (request a e)) ω x ω' <->
  ω' = gen_witness_update c ω e x /\ gen_callee_obligation c ω e x.
Proof. by rewrite to_hoare_requestE interface_to_hoare_postE. Qed.

Lemma to_hoare_request_postI `(e : ix a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω e x ->
  post (to_hoare (im:=im) c (request a e)) ω x
       (gen_witness_update c ω e x).
Proof. by rewrite to_hoare_requestE; exact: interface_to_hoare_postI. Qed.

(* ============ *)
Context `(p : im a) `(f : a -> im b).

Lemma to_hoare_bindE :
  to_hoare c (p >>= f) =
  to_hoare c p >>= fun x => to_hoare c (f x).
Proof. exact: denote_bind. Qed.

Lemma to_hoare_bind_preE (ω : Ω) :
  pre (to_hoare c (p >>= f)) ω <->
  pre (to_hoare c p) ω /\
  forall x ω',
    post (to_hoare c p) ω x ω' -> pre (to_hoare c (f x)) ω'.
Proof. by rewrite to_hoare_bindE hoare_bind_preE. Qed.

Lemma to_hoare_bind_preI (ω : Ω) :
  pre (to_hoare c p) ω ->
  (forall x ω',
    post (to_hoare c p) ω x ω' ->
    pre (to_hoare c (f x)) ω') ->
  pre (to_hoare c (p >>= f)) ω.
Proof. by move=> prefix suffix; apply/to_hoare_bind_preE; split. Qed.

Lemma to_hoare_bind_postE (ω : Ω) (y : b) (ω' : Ω) :
  post (to_hoare c (p >>= f)) ω y ω' <->
  exists x ω'',
    post (to_hoare c p) ω x ω'' /\ post (to_hoare c (f x)) ω'' y ω'.
Proof. by rewrite to_hoare_bindE hoare_bind_postE. Qed.

Lemma to_hoare_bind_postI
    (ω : Ω) (x : a) (ω'' : Ω) (y : b) (ω' : Ω) :
  post (to_hoare c p) ω x ω'' ->
  post (to_hoare c (f x)) ω'' y ω' ->
  post (to_hoare c (p >>= f)) ω y ω'.
Proof.
by move=> prefix suffix; apply/to_hoare_bind_postE; exists x, ω''.
Qed.

Lemma to_hoare_pre_bind_assoc
    `(Hp : pre (to_hoare c p) ω)
    (run : forall (x : a) (ω' : Ω),
      post (to_hoare c p) ω x ω' ->
      pre (to_hoare c (f x)) ω') :
  pre (to_hoare c (p >>= f)) ω.
Proof. exact/to_hoare_bind_preI. Qed.

Lemma to_hoare_post_bind_assoc
    `(Hp : post (to_hoare c (p >>= f)) ω x ω') :
  exists y ω'',
    post (to_hoare c p) ω y ω'' /\
    post (to_hoare c (f y)) ω'' x ω'.
Proof. exact/to_hoare_bind_postE. Qed.

End GenericHoareSection.

Module SpecializedHoareModule.
Section SpecializedHoareSection.
Context `{MayProvide ix i} `(c : contract i Ω).

Lemma to_hoare_localE `(x : a) : to_hoare c (pure x) = Ret x.
Proof. exact: denote_ret. Qed.

Lemma to_hoare_local_preE `(x : a) (ω : Ω) : pre (to_hoare c (pure x)) ω.
Proof. by rewrite to_hoare_localE hoare_pure_preE. Qed.

Lemma to_hoare_local_preI `(x : a) (ω : Ω) : pre (to_hoare c (pure x)) ω.
Proof. by apply/to_hoare_local_preE. Qed.

Lemma to_hoare_skip_preI (ω : Ω) :
  pre (to_hoare c (skip : freer ix unit)) ω.
Proof. exact: to_hoare_local_preI. Qed.

Lemma to_hoare_local_postE `(x : a) (y : a) (ω ω' : Ω) :
  post (to_hoare c (pure x)) ω y ω' <-> x = y /\ ω = ω'.
Proof. by rewrite to_hoare_localE hoare_pure_postE. Qed.

Lemma to_hoare_local_postI `(x : a) (ω : Ω) :
  post (to_hoare c (pure x)) ω x ω.
Proof. by apply/to_hoare_local_postE; split. Qed.

(* ========================================================================= *)
Context `(e : ix a) `(f : a -> freer ix b).

Lemma to_hoare_impure_preE (ω : Ω) :
  pre (to_hoare c (impure e f)) ω <->
  gen_caller_obligation c ω e /\ forall x, gen_callee_obligation c ω e x ->
    pre (to_hoare c (f x)) (gen_witness_update c ω e x).
Proof.
split.
- move=> /hoare_bind_preE [caller next]; split.
  + exact/interface_to_hoare_preE.
  + by move=> x callee; apply: next; exact/interface_to_hoare_postI.
- move=> [caller next]; apply/hoare_bind_preE; split.
  + exact/interface_to_hoare_preE.
  + by move=> x ω' /interface_to_hoare_postE [-> callee]; exact: next.
Qed.

Lemma to_hoare_impure_preI (ω : Ω) :
  gen_caller_obligation c ω e ->
  (forall x, gen_callee_obligation c ω e x ->
    pre (to_hoare c (f x)) (gen_witness_update c ω e x)) ->
  pre (to_hoare c (impure e f)) ω.
Proof. by move=> caller next; apply/to_hoare_impure_preE; split. Qed.

Lemma to_hoare_impure_postE (ω : Ω) (y : b) (ω' : Ω) :
  post (to_hoare c (impure e f)) ω y ω' <->
  exists x,
    post (to_hoare c (f x)) (gen_witness_update c ω e x) y ω' /\ gen_callee_obligation c ω e x.
Proof.
split.
- move=> /hoare_bind_postE [x [ω'' [+ suffix]]].
  rewrite interface_to_hoare_postE.
  by move=> [callee witness]; subst ω''; exists x.
- move=> [x [callee suffix]]; apply/hoare_bind_postE.
  by exists x, (gen_witness_update c ω e x); split.
Qed.

Lemma to_hoare_step `(hpre : pre (to_hoare c (impure e f)) ω)
    (x : a) (step : gen_callee_obligation c ω e x) :
  pre (to_hoare c (f x)) (gen_witness_update c ω e x).
Proof. by move: hpre => /to_hoare_impure_preE [_ +]; exact. Qed.

End SpecializedHoareSection.
End SpecializedHoareModule.

Import SpecializedHoareModule.


(** * Contract Product Views *)

Lemma contractprod_callerE `{Provide ix i, Provide ix j}
    `(ci : contract i Ωi) `(cj : contract j Ωj)
    (ωi : Ωi) (ωj : Ωj) `(e : ix a) :
  gen_caller_obligation (ci * cj) (ωi, ωj) e <->
  gen_caller_obligation ci ωi e /\ gen_caller_obligation cj ωj e.
Proof. by split. Qed.

Lemma contractprod_calleeE `{Provide ix i, Provide ix j}
    `(ci : contract i Ωi) `(cj : contract j Ωj)
    (ωi : Ωi) (ωj : Ωj) `(e : ix a) (x : a) :
  gen_callee_obligation (ci * cj) (ωi, ωj) e x <->
  gen_callee_obligation ci ωi e x /\
  gen_callee_obligation cj ωj e x.
Proof. by split. Qed.

Lemma contractprod_witnessE `{Provide ix i, Provide ix j}
    `(ci : contract i Ωi) `(cj : contract j Ωj)
    (ωi : Ωi) (ωj : Ωj) `(e : ix a) (x : a) :
  gen_witness_update (ci * cj) (ωi, ωj) e x =
  (gen_witness_update ci ωi e x, gen_witness_update cj ωj e x).
Proof. by []. Qed.

Lemma to_hoare_contractprod_preI `{Provide ix i, Provide ix j}
    `(ci : contract i Ωi) `(cj : contract j Ωj)
    `(p : freer ix a) (ωi : Ωi) (ωj : Ωj) :
  pre (to_hoare ci p) ωi ->
  pre (to_hoare cj p) ωj ->
  pre (to_hoare (ci * cj) p) (ωi, ωj).
Proof.
move: p ωi ωj.
elim=> [x | b e f ih] ωi ωj.
  by move=> _ _; apply/to_hoare_local_preE.
rewrite 2!to_hoare_impure_preE.
move=> [calleri nexti] [callerj nextj].
apply/to_hoare_impure_preI.
  by apply/contractprod_callerE; split.
move=> x /contractprod_calleeE [calleei calleej].
rewrite contractprod_witnessE.
apply: ih.
  exact: nexti calleei.
exact: nextj calleej.
Qed.

Lemma to_hoare_contractprod `{Provide ix i, Provide ix j}
    `(ci : contract i Ωi) `(cj : contract j Ωj)
    `(p : freer ix a) `(prei : pre (to_hoare ci p) ωi)
    `(prej : pre (to_hoare cj p) ωj) :
  pre (to_hoare (ci * cj) p) (ωi, ωj).
Proof. exact: to_hoare_contractprod_preI prei prej. Qed.

#[global] Hint Resolve to_hoare_contractprod_preI : freespec.

Lemma contract_equ_pre `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    `(equ : contract_equ c1 c2) (ω1 : Ω1) `(p : freer i A) :
  pre (to_hoare c1 p) ω1 <->
  pre (to_hoare c2 p) (contract_iso_lr equ ω1).
Proof.
elim: equ => f g iso1 iso2 caller_equ callee_equ witness_equ.
move: ω1.
elim: p=> [a | B e k IH] ω1.
- by split.
rewrite /= /gen_caller_obligation /gen_callee_obligation
  /gen_witness_update /=.
rewrite (caller_equ ω1 B e).
setoid_rewrite (callee_equ ω1 B e).
split => [[ocaller onext] | [ocaller onext]];
  split => // x ω1' [owitness ocallee].
- by rewrite owitness -witness_equ -IH; eauto.
rewrite IH; eauto.
rewrite owitness /= witness_equ; eauto.
Qed.

#[global] Hint Resolve contract_equ_pre : freespec.

Lemma contract_equ_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1)
    `(p : freer i A) (x : A)
    (post1 : post (to_hoare c1 p) ω1 x ω1') :
  post (to_hoare c2 p) (contract_iso_lr equ ω1) x
       (contract_iso_lr equ ω1').
Proof.
elim: equ => [f g iso1 iso2 caller_equ callee_equ witness_equ].
move: p x ω1 ω1' post1.
elim=> [in_a | B e k ih].
- by move=> a ω1 ω1' [<- <-].
move=> a ω1 ω1' [b [ω1'' [[ow oc] +]]] /= => /ih post1.
exists b, (f ω1''); split; [split|exact: post1].
- by rewrite ow witness_equ.
- exact/(callee_equ ω1 B e).
Qed.

#[global] Hint Resolve contract_equ_post : freespec.
