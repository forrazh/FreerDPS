(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From mathcomp Require Import ssreflect.
From FreerDPS Require Import Interface Impure Contract Hoare.
From monae Require Import preamble hierarchy.
Generalizable All Variables.

(** * Primitive Request Views *)

Lemma interface_to_hoare_preE `{MayProvide ix i} `(c : contract i Ω)
    `(e : ix a) (ω : Ω) :
  pre (interface_to_hoare c e) ω <-> gen_caller_obligation c ω e.
Proof. by split. Qed.

Lemma interface_to_hoare_postE `{MayProvide ix i} `(c : contract i Ω)
    `(e : ix a) (ω : Ω) (x : a) (ω' : Ω) :
  post (interface_to_hoare c e) ω x ω' <->
  gen_callee_obligation c ω e x /\
  ω' = gen_witness_update c ω e x.
Proof. by split. Qed.

Lemma interface_to_hoare_postI `{MayProvide ix i} `(c : contract i Ω)
    `(e : ix a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω e x ->
  post (interface_to_hoare c e) ω x
       (gen_witness_update c ω e x).
Proof. by move=> step; split. Qed.

Lemma to_hoare_requestE `{MayProvide ix i} {im : impureMonad ix}
    `(c : contract i Ω) `(e : ix a) :
  to_hoare (im:=im) c (request a e) = interface_to_hoare c e.
Proof. exact: impure_lift_request. Qed.

Lemma to_hoare_request_preE `{MayProvide ix i} {im : impureMonad ix}
    `(c : contract i Ω) `(e : ix a) (ω : Ω) :
  pre (to_hoare (im:=im) c (request a e)) ω <->
  gen_caller_obligation c ω e.
Proof. by rewrite to_hoare_requestE interface_to_hoare_preE. Qed.

Lemma to_hoare_request_postE `{MayProvide ix i} {im : impureMonad ix}
    `(c : contract i Ω) `(e : ix a) (ω : Ω) (x : a) (ω' : Ω) :
  post (to_hoare (im:=im) c (request a e)) ω x ω' <->
  gen_callee_obligation c ω e x /\
  ω' = gen_witness_update c ω e x.
Proof. by rewrite to_hoare_requestE interface_to_hoare_postE. Qed.

Lemma to_hoare_request_postI `{MayProvide ix i} {im : impureMonad ix}
    `(c : contract i Ω) `(e : ix a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω e x ->
  post (to_hoare (im:=im) c (request a e)) ω x
       (gen_witness_update c ω e x).
Proof. by rewrite to_hoare_requestE; exact: interface_to_hoare_postI. Qed.

Lemma pair_eqE {A B} (x x' : A) (y y' : B) :
  (x, y) = (x', y') -> x = x' /\ y = y'.
Proof. by move=> [] /=; split. Qed.

(** * General Lemmas *)

Lemma to_hoare_step `{MayProvide ix i} `(c : contract i Ω)
   `(e : ix a) `(f : a -> impure ix a)
   `(hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (request_then e f)) ω)
    (x : a) (step : gen_callee_obligation c ω e x)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (f x)) (gen_witness_update c ω e x).

Proof.
  by case: hpre=> [_ next]; apply/next/interface_to_hoare_postI.
Qed.

#[global] Hint Resolve to_hoare_step : freespec.

Lemma to_hoare_pre_bind_assoc `{MayProvide ix i} `(c : contract i Ω)
   `(p : impure ix a) `(Hp : pre (to_hoare  (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c p) ω)
   `(f : a -> impure ix b)
    (run : forall (x : a) (ω' : Ω),
        post (to_hoare  (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c p) ω x ω' -> pre (to_hoare  (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (f x)) ω')
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (impure_bind p f)) ω.

Proof.
  move: p ω Hp run.
  elim=>/=[in_a | Y e k IH] ω Hp run.
  + by apply: run; split.
  + move: Hp=> [caller next]; split=> // x ω' [callee witness]; apply: IH => [| y ω''].
    ++ by apply: next; split.
    ++ move: witness run => -> + Hnext; apply.
       exists x, (gen_witness_update c ω e x).
       by split; last exact: Hnext; split.
Qed.

Lemma to_hoare_post_bind_assoc `{MayProvide ix i} `(c : contract i Ω)
   `(p : impure ix a) `(f : a -> impure ix b)
   `(Hp : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (impure_bind p f)) ω x ω')
  : exists y ω'',
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c p) ω y ω'' /\ post (to_hoare c (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) $ f y) ω'' x ω'.

Proof.
  move: p ω Hp; elim=> [in_a | Y e k IH] ω.
  - by exists in_a, ω.
  by move=> [y [ω'' [ostep +]]]=> /IH [z [ω''' [Hprefix Hsuffix]]];
    exists z, ω'''; split=> //; exists y, ω''; split.
Qed.

Lemma to_hoare_contractprod `{Provide ix i, Provide ix j}
   `(ci : contract i Ωi) `(cj : contract j Ωj)
   `(p : impure ix a)
   `(prei : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) ci p) ωi) `(prej : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) cj p) ωj)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (ci * cj) p) (ωi, ωj).

Proof.
  move: p ωi prei ωj prej; elim=> //= Y e k IH ωi [calleri nexti] ωj [callerj nextj]; split => [|].
  + exact: (conj calleri callerj).
  move=> y [ωi' ωj']; rewrite -interface_to_hoare_postE=> [[[calleei calleej] witnesses]].
  have [wi wj] := pair_eqE _ _ _ _ witnesses.
  
  by move: IH witnesses wi wj=> + -> ??; 
    apply; [apply: nexti | apply: nextj]; 
    rewrite -interface_to_hoare_postE; split.
Qed.

#[global] Hint Resolve to_hoare_contractprod : freespec.

Lemma contract_equ_pre `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : contract_equ c1 c2) (ω1 : Ω1)
   `(p : impure i A)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c1 p) ω1 <-> pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c2 p) (contract_iso_lr equ ω1).

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
  split => // x ω1' [ocallee owitness].
  - by rewrite owitness -witness_equ -IH; eauto.
  rewrite IH; eauto.
  rewrite owitness /= witness_equ; eauto.
Qed.

#[global] Hint Resolve contract_equ_pre : freespec.

Lemma contract_equ_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1)
   `(p : impure i A) (x : A)
    (post1 : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c1 p) ω1 x ω1')
  : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c2 p) (contract_iso_lr equ ω1) x (contract_iso_lr equ  ω1').

Proof.
  elim:equ=> [f g iso1 iso2 caller_equ callee_equ witness_equ].
  move: p x ω1 ω1' post1.
  elim=>[in_a | B e k IH]=> a ω1 ω1' [b witness] /=.
  + by subst a; subst ω1'; split.
  + move: witness=> [ω1'' [[ocallee owitness] +]] /= => /IH post1.
    exists b, (f ω1''); split; [split|exact: post1].
    ++ exact/(callee_equ ω1 B e).
    ++ by rewrite owitness witness_equ.
Qed.

#[global] Hint Resolve contract_equ_post : freespec.
