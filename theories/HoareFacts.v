(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

Attributes deprecated(
  note="The contents of this file will be moved to `Hoare.v`.").

From FreerDPS Require Import Init Effect Freer Contract Hoare.
Generalizable All Variables.

Local Open Scope monae_scope.

(** * Hoare Interpretation Views *)

Section GenericHoareSection.
Variable Fx : effect.
Context `{MayProvide Fx F} {im : freerMonad Fx} `(c : contract F Ω).

(* Lemma hoare_of_contract_preE `(op : Fx a) (ω : Ω) :
  pre (hoare_of_contract c op) ω <-> gen_caller_obligation c ω op.
Proof. by split. Qed.

Lemma hoare_of_contract_postE `(op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  post (hoare_of_contract c op) ω x ω' <->
  ω' = gen_witness_update c ω op x /\
  gen_callee_obligation c ω op x.
Proof. by split. Qed.

Lemma hoare_of_contract_postI `(op : Fx a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω op x ->
  post (hoare_of_contract c op) ω x (gen_witness_update c ω op x).
Proof. by move=> step; split. Qed. *)

Lemma to_hoare_requestE `(op : Fx a) :
  to_hoare (im:=im) c (request a op) = hoare_of_contract c op.
Proof. exact: denote_request. Qed.

(* Lemma to_hoare_request_preE `(op : Fx a) (ω : Ω) :
  pre (to_hoare (im:=im) c (request a op)) ω <->
  gen_caller_obligation c ω op.
Proof. by rewrite to_hoare_requestE hoare_of_contract_preE. Qed.

Lemma to_hoare_request_postE `(op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  post (to_hoare (im:=im) c (request a op)) ω x ω' <->
  ω' = gen_witness_update c ω op x /\ gen_callee_obligation c ω op x.
Proof. by rewrite to_hoare_requestE hoare_of_contract_postE. Qed.

Lemma to_hoare_request_postI `(op : Fx a) (ω : Ω) (x : a) :
  gen_callee_obligation c ω op x ->
  post (to_hoare (im:=im) c (request a op)) ω x
       (gen_witness_update c ω op x).
Proof. by rewrite to_hoare_requestE; exact: hoare_of_contract_postI. Qed. *)

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
Variable Fx : effect.
Context `{MayProvide Fx F} `(c : contract F Ω).

Lemma to_hoare_localE `(x : a) : (pure x |= c) = Ret x.
Proof. exact: denote_ret. Qed.

Lemma to_hoare_local_preE `(x : a) (ω : Ω) : pre (pure x |= c) ω.
Proof. by rewrite to_hoare_localE hoare_pure_preE. Qed.

Lemma to_hoare_local_preI `(x : a) (ω : Ω) : pre (pure x |= c) ω.
Proof. by apply/to_hoare_local_preE. Qed.

(* Lemma to_hoare_skip_preI (ω : Ω) :
  pre (to_hoare c (skip : freer Fx unit)) ω.
Proof. exact: to_hoare_local_preI. Qed. *)

Lemma to_hoare_local_postE `(x : a) (y : a) (ω ω' : Ω) :
  post (pure x |= c) ω y ω' <-> x = y /\ ω = ω'.
Proof. by rewrite to_hoare_localE hoare_pure_postE. Qed.

Lemma to_hoare_local_postI `(x : a) (ω : Ω) :
  post (pure x |= c) ω x ω.
Proof. by apply/to_hoare_local_postE; split. Qed.

(* ========================================================================= *)
Context `(op : Fx a) `(f : a -> freer Fx b).

(* Lemma to_hoare_impure_preE (ω : Ω) :
  pre (to_hoare c (impure op f)) ω <->
  gen_caller_obligation c ω op /\ forall x, gen_callee_obligation c ω op x ->
    pre (to_hoare c (f x)) (gen_witness_update c ω op x).
Proof.
split.
- move=> /hoare_bind_preE [caller next]; split.
  + exact/hoare_of_contract_preE.
  + by move=> x callee; apply: next; exact/hoare_of_contract_postI.
- move=> [caller next]; apply/hoare_bind_preE; split.
  + exact/hoare_of_contract_preE.
  + by move=> x ω' /hoare_of_contract_postE [-> callee]; exact: next.
Qed.

Lemma to_hoare_impure_preI (ω : Ω) :
  gen_caller_obligation c ω op ->
  (forall x, gen_callee_obligation c ω op x ->
    pre (to_hoare c (f x)) (gen_witness_update c ω op x)) ->
  pre (to_hoare c (impure op f)) ω.
Proof. by move=> caller next; apply/to_hoare_impure_preE; split. Qed.

Lemma to_hoare_impure_postE (ω : Ω) (y : b) (ω' : Ω) :
  post (to_hoare c (impure op f)) ω y ω' <->
  exists x,
    post (to_hoare c (f x)) (gen_witness_update c ω op x) y ω' /\
    gen_callee_obligation c ω op x.
Proof.
split.
- move=> /hoare_bind_postE [x [ω'' [+ suffix]]].
  rewrite hoare_of_contract_postE.
  by move=> [callee witness]; subst ω''; exists x.
- move=> [x [callee suffix]]; apply/hoare_bind_postE.
  by exists x, (gen_witness_update c ω op x); split.
Qed.

Lemma to_hoare_step `(hpre : pre (to_hoare c (impure op f)) ω)
    (x : a) (step : gen_callee_obligation c ω op x) :
  pre (to_hoare c (f x)) (gen_witness_update c ω op x).
Proof. by move: hpre => /to_hoare_impure_preE [_ +]; exact. Qed. *)

End SpecializedHoareSection.
End SpecializedHoareModule.

Import SpecializedHoareModule.


(** * Contract Product Views *)

(* Lemma contractprod_callerE {Fx : effect} `{Provide Fx F, Provide Fx E}
    `(cF : contract F ΩF) `(cE : contract E ΩE)
    (ωF : ΩF) (ωE : ΩE) `(op : Fx a) :
  gen_caller_obligation (cF * cE) (ωF, ωE) op <->
  gen_caller_obligation cF ωF op /\ gen_caller_obligation cE ωE op.
Proof. by split. Qed.

Lemma contractprod_calleeE {Fx : effect} `{Provide Fx F, Provide Fx E}
    `(cF : contract F ΩF) `(cE : contract E ΩE)
    (ωF : ΩF) (ωE : ΩE) `(op : Fx a) (x : a) :
  gen_callee_obligation (cF * cE) (ωF, ωE) op x <->
  gen_callee_obligation cF ωF op x /\
  gen_callee_obligation cE ωE op x.
Proof. by split. Qed.

Lemma contractprod_witnessE {Fx : effect} `{Provide Fx F, Provide Fx E}
    `(cF : contract F ΩF) `(cE : contract E ΩE)
    (ωF : ΩF) (ωE : ΩE) `(op : Fx a) (x : a) :
  gen_witness_update (cF * cE) (ωF, ωE) op x =
  (gen_witness_update cF ωF op x, gen_witness_update cE ωE op x).
Proof. by []. Qed. *)

(* Lemma to_hoare_contractprod_preI
    {Fx : effect} `{Provide Fx F, Provide Fx E}
    `(cF : contract F ΩF) `(cE : contract E ΩE)
    `(p : freer Fx a) (ωF : ΩF) (ωE : ΩE) :
  pre (to_hoare cF p) ωF ->
  pre (to_hoare cE p) ωE ->
  pre (to_hoare (cF * cE) p) (ωF, ωE).
Proof.
move: p ωF ωE.
elim=> [x | b op f ih] ωF ωE.
  by move=> _ _; apply/to_hoare_local_preE.
rewrite 2!to_hoare_impure_preE.
move=> [callerF nextF] [callerE nextE].
apply/to_hoare_impure_preI.
  by apply/contractprod_callerE; split.
move=> x /contractprod_calleeE [calleeF calleeE].
rewrite contractprod_witnessE.
apply: ih.
  exact: nextF calleeF.
exact: nextE calleeE.
Qed.

Lemma to_hoare_contractprod {Fx : effect} `{Provide Fx F, Provide Fx E}
    `(cF : contract F ΩF) `(cE : contract E ΩE)
    `(p : freer Fx a) `(preF : pre (to_hoare cF p) ωF)
    `(preE : pre (to_hoare cE p) ωE) :
  pre (to_hoare (cF * cE) p) (ωF, ωE).
Proof. exact: to_hoare_contractprod_preI preF preE. Qed.

#[global] Hint Resolve to_hoare_contractprod_preI : freespec.
*)

Lemma contract_equ_pre `(c1 : contract F Ω1) `(c2 : contract F Ω2)
    `(equ : contract_equ c1 c2) (ω1 : Ω1) `(p : freer F A) :
  pre (to_hoare c1 p) ω1 <->
  pre (to_hoare c2 p) (contract_iso_lr equ ω1).
Proof.
elim: equ => f g iso1 iso2 caller_equ callee_equ witness_equ.
move: ω1.
elim: p=> [a | B op k IH] ω1.
- by split.
rewrite /= /gen_caller_obligation /gen_callee_obligation
  /gen_witness_update /=.
rewrite (caller_equ ω1 B op).
setoid_rewrite (callee_equ ω1 B op).
split => [[ocaller onext] | [ocaller onext]];
  split => // x ω1' [owitness ocallee].
- by rewrite owitness -witness_equ -IH; eauto.
rewrite IH; eauto.
rewrite owitness /= witness_equ; eauto.
Qed.

#[global] Hint Resolve contract_equ_pre : freespec.

Lemma contract_equ_post `(c1 : contract F Ω1) `(c2 : contract F Ω2)
    `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1)
    `(p : freer F A) (x : A)
    (post1 : post (to_hoare c1 p) ω1 x ω1') :
  post (to_hoare c2 p) (contract_iso_lr equ ω1) x
       (contract_iso_lr equ ω1').
Proof.
elim: equ => [f g iso1 iso2 caller_equ callee_equ witness_equ].
move: p x ω1 ω1' post1.
elim=> [in_a | B op k ih].
- by move=> a ω1 ω1' [<- <-].
move=> a ω1 ω1' [b [ω1'' [[ow oc] +]]] /= => /ih post1.
exists b, (f ω1''); split; [split|exact: post1].
- by rewrite ow witness_equ.
- exact/(callee_equ ω1 B op).
Qed.

#[global] Hint Resolve contract_equ_post : freespec.
