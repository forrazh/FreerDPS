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

(** ** Invariant Preservation *)

Definition preserves_invariant {S A}
    (invariant : set S) (h : hoare S A) :=
  forall state result state',
    pre h state ->
    post h state result state' ->
    invariant state ->
    invariant state'.

Lemma preserves_invariant_ret {S A}
    (invariant : set S) (result : A) :
  preserves_invariant invariant (@ret (hoare S) A result).
Proof. by move=>???? [_ <-]. Qed.

Lemma preserves_invariant_bind {S A B} (invariant : set S)
    (h : hoare S A) (k : A -> hoare S B) :
  preserves_invariant invariant h ->
  (forall result, preserves_invariant invariant (k result)) ->
  preserves_invariant invariant (h >>= k).
Proof.
move=> h_preserves k_preserves ??? [h_pre k_pre] [? [? [h_post k_post]]] Hsafe.
apply: k_preserves.
- exact/k_pre/h_post.
- exact: k_post.
by move: h_pre h_post Hsafe; exact: h_preserves.
Qed.

Lemma denote_preserves_invariant {Fx : effect} {M : inductiveFreerMonad Fx}
  {S : UU0} (invariant : set S) (handler : Fx ~~> hoare S) (A : UU0) (p : M A) :
  (forall (X : Type) (op : Fx X),
    preserves_invariant invariant (handler _ op)) ->
  preserves_invariant invariant
    (denote (hoare S) handler A p).
Proof.
move=> H s a s'.
apply: (@denote_ind _ _ _ _  (fun X => preserves_invariant invariant)).
- move=> X x.
  exact: preserves_invariant_ret.
- move=> X Y h k h_preserves k_preserves.
  exact: preserves_invariant_bind h_preserves k_preserves.
- exact: H.
Qed.

(** * Reasoning about Programs *)

Definition hoare_of_contract {Fx F : effect} `{F -<? Fx}
    (Ω : Type) (c : contract F Ω)
    : Fx ~~> hoare Ω :=
  fun a op => mk_hoare
    (gen_caller_obligation c ^~ op)
    (fun ω x ω' => ω' = gen_witness_update c ω op x /\
                  gen_callee_obligation c ω' op x).
Arguments hoare_of_contract : simpl never.

Definition to_hoare {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω)
    : M ~~> hoare Ω :=
  denote _ (hoare_of_contract c).
Arguments to_hoare {Fx F _ M Ω} c {α} : rename, simpl never.

(** A Hoare triple can be interpreted from the program `p`
  * through the contract `c`.
  *)
Notation "c |> p" := (to_hoare c p)
  (at level 50, no associativity).

(* --------------------------------- Facts ---------------------------------- *)

Section GenericToHoareSection.
Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω).

Lemma to_hoare_triggerE (a : Type) (op : Fx a) :
  (c |> (trigger a op : M _)) = hoare_of_contract c op.
Proof. exact: denote_trigger. Qed.

Lemma to_hoare_ret_preI {A : Type} (x : A) (ω : Ω) :
  pre (c |> (Ret x : M A)) ω.
Proof. by rewrite /to_hoare denote_ret. Qed.

Lemma to_hoare_ret_postE {A : Type}
    (value result : A) (ω ω' : Ω) :
  post (c |> (Ret value : M A)) ω result ω' <->
  value = result /\ ω = ω'.
Proof. by rewrite /to_hoare denote_ret. Qed.

Section BindFacts.
Context {a b : Type} (p : M a) (f : a -> M b).

Lemma to_hoare_bindE :
  c |> (p >>= f) =
  (c |> p) >>= (fun x => c |> (f x)).
Proof. exact: denote_bind. Qed.

(* TODO: Check if it is WP  *)
Lemma pre_to_hoare_bind (ω : Ω) :
  pre (c |> p) ω ->
  (forall x ω',
    post (c |> p) ω x ω' ->
    pre (c |> (f x)) ω') ->
  pre (c |> (p >>= f)) ω.
Proof. by move=> prefix suffix; rewrite to_hoare_bindE hoare_bindE; split. Qed.

Lemma post_to_hoare_bindP (ω : Ω) (y : b) (ω' : Ω) :
  post (c |> (p >>= f)) ω y ω' <->
  exists x ω'',
    post (c |> p) ω x ω'' /\ post (c |> (f x)) ω'' y ω'.
Proof. by rewrite to_hoare_bindE hoare_bindE. Qed.

End BindFacts.

Section WhenFacts.
Context {a : Type} (p : M a) (guard : bool).

Lemma pre_to_hoare_whenP (ω : Ω) :
  pre (c |> when guard p) ω <-> if guard then pre (c |> p) ω else True.
Proof.
by case: guard=> /=;
  [rewrite to_hoare_bindE; split=> [[ ] | ] //|];
  split=> // *; exact: to_hoare_ret_preI.
Qed.

Lemma post_to_hoare_whenP (ω : Ω) (x : unit) (ω' : Ω) :
  post (c |> when guard p) ω x ω' <->
  if guard
  then exists y, post (c |> p) ω y ω'
  else ω' = ω.
Proof.
case: x; case: guard=> /=;
  rewrite ?post_to_hoare_bindP /to_hoare denote_ret;
  last first.
- by split=> [[_ ->] | <-].
by split=> [[y [? [? [_ <-]]]] | [y ?]];
  exists y=>//;
  exists ω'; split.
Qed.

End WhenFacts.

End GenericToHoareSection.

Lemma to_hoare_preserves_invariant {Fx F : effect} `{F -<? Fx}
  {M : inductiveFreerMonad Fx} {S : UU0}
  (invariant : set S) (c : contract F S)
  (handler_preserves : forall (A : UU0) (op : Fx A),
    preserves_invariant invariant (hoare_of_contract c op)) (A : UU0) (p : M A) :
  preserves_invariant invariant (c |> p).
Proof. exact: denote_preserves_invariant. Qed.

(** ** Trigger Views *)

Section contract_trigger_helpers.
Context {Fx F : effect} `{F -< Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω) {A : Type}.

Lemma pre_to_hoare_triggerP (op : F A) (ω : Ω) :
  pre (to_hoare (M:=M) c (ptrigger op)) ω <->
  caller_obligation c ω op.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Lemma post_to_hoare_triggerP (op : F A) (ω : Ω) (a : A) (ω' : Ω) :
  post (to_hoare (M:=M) c (ptrigger op))
    ω a ω' <->
  ω' = witness_update c ω op a /\
  callee_obligation c ω' op a.
Proof. by rewrite to_hoare_triggerE /= provided_calleeP. Qed.

End contract_trigger_helpers.

(** ** Shared Contract Trigger Views *)

Section ToHoareSharedContractSection.
Context {F G H : effect} `{F ;; G -<< H}
    {M : freerMonad H} (Ω : Type) (ci : contract F Ω)
    (cj : contract G Ω).

Lemma pre_to_hoare_triggerL
    {A : Type} (op : F A) (ω : Ω) :
  caller_obligation ci ω op ->
  pre (to_hoare (M:=M)
    (ci -^- cj) (ptrigger op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_left_callerP. Qed.

Lemma pre_to_hoare_triggerR
    {A : Type} (op : G A) (ω : Ω) :
  caller_obligation cj ω op ->
  pre (to_hoare (M:=M)
    (ci -^- cj) (ptrigger op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_right_callerP. Qed.

Lemma post_to_hoare_triggerLP
    {A : Type} (op : F A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (ci -^- cj) (ptrigger op)) ω x ω' <->
  ω' = witness_update ci ω op x /\
  callee_obligation ci ω' op x.
Proof. by rewrite to_hoare_triggerE /= shared_left_calleeP. Qed.

Lemma post_to_hoare_triggerRP
    {A : Type} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (ci -^- cj) (ptrigger op)) ω x ω' <->
  ω' = witness_update cj ω op x /\
  callee_obligation cj ω' op x.
Proof. by rewrite to_hoare_triggerE /= shared_right_calleeP. Qed.
End ToHoareSharedContractSection.
