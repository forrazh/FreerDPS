(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra Init effect freer Contract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** To reason about impure computations, we introduce the “Hoare
    monad,” also called the “specification monad.” An instance of the
    specification monad is a couple of [pre] and [post] conditions,
    such that [pre p σ] means the program specified by [p] can be
    executed safely from a state [σ], and [post p σ x σ'] means the
    execution of [p] from [σ] may compute a result [x] and bring the
    system to a state [σ'].

    We equip this couple of predicate with a [bind] function to
    sequentially compose specifications. *)

(** * Definition *)

Record hoare (Σ : Type) (α : Type) : Type := mk_hoare {
  pre : set Σ ;
  post : Σ -> α -> set Σ }.

Arguments mk_hoare {Σ α} (pre post).
Arguments pre {Σ α} (_ _).
Arguments post {Σ α} (_ _ _).

Definition hoare_pure {Σ α} (x : α) : hoare Σ α :=
  mk_hoare [set: Σ] (fun s y s' => x = y /\ s = s').

Definition hoare_bind {Σ α β}
    (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
  mk_hoare (fun s => pre h s /\ (forall x s', post h s x s' -> pre (k x) s'))
           (fun s x s'' => exists y s', post h s y s' /\ post (k y) s' x s'').

Definition hoare_map {Σ α β} (f : α -> β) (h : hoare Σ α) : hoare Σ β :=
  hoare_bind h (fun x => hoare_pure (f x)).

Definition hoare_apply {Σ α β} (hf : hoare Σ (α -> β)) (h : hoare Σ α)
  : hoare Σ β :=
  hoare_bind hf (fun f => hoare_map f h).

(** ** Monad *)

(** Easier to had future laws from there. *)
HB.mixin Record isMonadHoare (S : Type)
    (M : Type -> Type) of Monad M := {}.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (S : Type) :=
  {M of isMonadHoare S M &}.

Module hoare_mon.
Section hm.
Variable Σ : Type.
Let ret := @hoare_pure Σ.
Let bind := @hoare_bind Σ.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_pure/=; congr mk_hoare.
- by apply/funext => s/=; apply/propext; split; tauto.
- apply/eq3_fun => s a s''.
  under eq2_exists do rewrite andA.
  by rewrite ex2C ex2_eqr ex_eqr.
Qed.

(* Local Open Scope ssripat_scope. *)

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind /ret /hoare_bind /hoare_pure/=.
move fa : (f a) => [pr po]; congr mk_hoare.
- apply/funext=> s; rewrite andTP; apply/propext; split.
  + by move=> /(_ a s); rewrite fa/=; exact.
  + by move=> prs _ _ [<- <-]; rewrite fa.
- apply/eq3_fun => s b s'.
  under eq2_exists do rewrite andC andA.
  rewrite ex2C.
  under eq_exists do rewrite ex_andl.
  by rewrite ex_eqr_sym ex_eqr_sym fa.
Qed.

Let assoc : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind /ret /hoare_bind /hoare_pure/=.
case: m => prA poA/=; congr mk_hoare.
- apply/funext => s; apply/propext; split.
  + move=> [[prAs poApre postpre]].
    split => // a s1 sas1; split=> [|b s2 s'bs2].
      exact: poApre.
    by apply: postpre; exists a, s1.
  + move=> [prAs poApre]; split.
      by split=> // a s1 /poApre[].
    move=> b s1 [x [s2]] [] /poApre [fxs2] /[swap] s2bs1.
    exact.
- apply: eq3_fun => s c s1.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => a.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => s2.
  rewrite -ex_andr.
  under [in RHS]eq_exists do rewrite -ex_andr.
  by under [in RHS]eq2_exists do rewrite andA.
Qed.

HB.instance Definition _ := isMonad_ret_bind.Build (hoare Σ)
  left_neutral right_neutral assoc.

End hm.
End hoare_mon.

HB.export hoare_mon.

HB.instance Definition _ (S : Type) :=
  isMonadHoare.Build S (hoare S).

(** ** Primitive Views *)

Lemma hoare_bindE {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) :
  @bind (hoare Σ) α β h k = hoare_bind h k.
Proof. by []. Qed.

(** This actually may not be really useful as we reason
  * either on pre or on post cond.
  *)
Lemma hoare_ext {Σ α} (h1 h2 : hoare Σ α) :
  (forall s, pre h1 s <-> pre h2 s) ->
  (forall s x s', post h1 s x s' <-> post h2 s x s') ->
  h1 = h2.
Proof.
  case: h1 => pre1 post1; case: h2 => pre2 post2.
  move=> pre_equiv post_equiv /=.
  congr mk_hoare.
  - apply/boolp.funext=> s.
    exact/boolp.propext/pre_equiv.
  apply/eq3_fun=> s x s'.
  exact/boolp.propext/post_equiv.
Qed.

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

Lemma denote_preserves_invariant {Fx : eff} {M : inductiveFreerMonad Fx}
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

Definition hoare_of_contract {Fx F : eff} `{F -<? Fx}
    (Ω : Type) (c : contract F Ω)
    : Fx ~~> hoare Ω :=
  fun a op => mk_hoare
    (gen_caller_obligation c ^~ op)
    (fun ω x ω' => ω' = gen_witness_update c ω op x /\
                  gen_callee_obligation c ω op x).

(** ** Contract Views *)

Section contract_eff_views.
Context {Fx F : eff} `{F -<? Fx}
    (Ω : Type) (c : contract F Ω) {A : Type}.

Lemma hoc_eff_preE (operation : Fx A) (witness : Ω) :
  pre (hoare_of_contract c operation) witness <->
  if prj operation is Some eff_operation then
    caller_obligation c witness eff_operation
  else
    True.
Proof. by []. Qed.

Lemma hoc_eff_postE
    (operation : Fx A) (witness : Ω) (result : A) (witness' : Ω) :
  post (hoare_of_contract c operation) witness result witness' <->
  match prj operation with
  | Some eff_operation =>
      witness' = witness_update c witness eff_operation result /\
      callee_obligation c witness eff_operation result
  | None => witness' = witness
  end.
Proof.
rewrite /= /gen_witness_update /gen_callee_obligation.
case: prj => //=.
by split=> [[-> _] | ->].
Qed.

End contract_eff_views.
Section contract_operation_views.
Context {Fx F : eff} `{F -< Fx}
    (Ω : Type) (c : contract F Ω) {A : Type}.

Lemma hoc_pre_condE (witness : Ω) (operation : F A) :
  pre (hoare_of_contract (Fx:=Fx) c (inj operation)) witness <->
  caller_obligation c witness operation.
Proof. by rewrite hoc_eff_preE injK_Some. Qed.

Lemma hoc_post_condE
    (witness : Ω) (operation : F A) (result : A) (witness' : Ω) :
  post (hoare_of_contract (Fx:=Fx) c (inj operation))
    witness result witness' <->
  witness' = witness_update c witness operation result /\
  callee_obligation c witness operation result.
Proof. by rewrite hoc_eff_postE injK_Some. Qed.

End contract_operation_views.

(** ** Program Interpretation *)

Definition to_hoare {Fx F : eff} `{F -<? Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω)
    : M ~~> hoare Ω :=
  denote _ (hoare_of_contract c).
Arguments to_hoare {Fx F _ M Ω} c {α} : rename.

(** A Hoare triple can be interpreted from the program `p`
  * through the contract `c`.
  *)
Notation "c |> p" := (to_hoare c p)
  (at level 50, no associativity).

(* --------------------------------- Facts ---------------------------------- *)

Section GenericToHoareSection.
Context {Fx F : eff} `{F -<? Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω).

Lemma to_hoare_triggerE (a : Type) (op : Fx a) :
  to_hoare (M:=M) c (trigger a op) = hoare_of_contract c op.
Proof. exact: denote_trigger. Qed.

Lemma to_hoare_trigger_preE (a : Type) (op : Fx a) (ω : Ω) :
  pre (to_hoare (M:=M) c (trigger a op)) ω <->
  if prj op is Some eff_op then  caller_obligation c ω eff_op else True.
Proof. by rewrite to_hoare_triggerE hoc_eff_preE. Qed.

Lemma to_hoare_trigger_postE
    (a : Type) (op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  post (to_hoare (M:=M) c (trigger a op)) ω x ω' <->
  match prj op with
  | Some eff_operation =>
      ω' = witness_update c ω eff_operation x /\
      callee_obligation c ω eff_operation x
  | None => ω' = ω
  end.
Proof. by rewrite to_hoare_triggerE hoc_eff_postE. Qed.

Lemma to_hoare_skip_preI (ω : Ω) :
  pre (c |> (skip : M unit)) ω.
Proof. by rewrite /to_hoare denote_ret. Qed.

Lemma to_hoare_skip_postE (ω : Ω) x ω' :
  post (c |> (skip : M unit)) ω x ω' <-> post (Ret tt) ω x ω'.
Proof. by rewrite /to_hoare denote_ret. Qed.

Section BindFacts.
Context {a b : Type} (p : M a) (f : a -> M b).

Lemma to_hoare_bindE :
  to_hoare c (p >>= f) =
  to_hoare c p >>= fun x => to_hoare c (f x).
Proof. exact: denote_bind. Qed.

Lemma th_pre_bindA (ω : Ω) :
  pre (to_hoare c p) ω ->
  (forall x ω',
    post (to_hoare c p) ω x ω' ->
    pre (to_hoare c (f x)) ω') ->
  pre (to_hoare c (p >>= f)) ω.
Proof. by move=> prefix suffix; rewrite to_hoare_bindE hoare_bindE; split. Qed.

Lemma th_post_bindA (ω : Ω) (y : b) (ω' : Ω) :
  post (to_hoare c (p >>= f)) ω y ω' <->
  exists x ω'',
    post (to_hoare c p) ω x ω'' /\ post (to_hoare c (f x)) ω'' y ω'.
Proof. by rewrite to_hoare_bindE hoare_bindE. Qed.

End BindFacts.

Section WhenFacts.
Context {a : Type} (p : M a) (guard : bool).

Lemma to_hoare_when_preE (ω : Ω) :
  pre (c |> when guard p) ω <->
  if guard then pre (c |> p) ω else True.
Proof.
by case: guard=> /=;
  [rewrite to_hoare_bindE; split=> [[ ] | ] //|];
  split=> // *; exact: to_hoare_skip_preI.
Qed.

Lemma to_hoare_when_postE (ω : Ω) (x : unit) (ω' : Ω) :
  post (c |> when guard p) ω x ω' <->
  if guard
  then exists y, post (c |> p) ω y ω'
  else ω' = ω.
Proof.
case: x; case: guard=> /=;
  rewrite ?th_post_bindA /to_hoare denote_ret;
  last first.
- by split=> [[_ ->] | <-].
by split=> [[y [? [? [_ <-]]]] | [y ?]];
  exists y=>//;
  exists ω'; split.
Qed.

End WhenFacts.
End GenericToHoareSection.

Lemma to_hoare_preserves_invariant {Fx F : eff} `{F -<? Fx}
  {M : inductiveFreerMonad Fx} {S : UU0}
  (invariant : set S) (c : contract F S)
  (handler_preserves : forall (A : UU0) (op : Fx A),
    preserves_invariant invariant (hoare_of_contract c op)) (A : UU0) (p : M A) :
  preserves_invariant invariant (c |> p).
Proof. exact: denote_preserves_invariant. Qed.

(** ** Trigger Views *)

Section contract_trigger_helpers.
Context {Fx F : eff} `{F -< Fx} {M : freerMonad Fx}
    (Ω : Type) (c : contract F Ω) {A : Type}.

Lemma to_hoare_ptrigger_preE (op : F A) (ω : Ω) :
  pre (to_hoare (M:=M) c (ptrigger op)) ω <->
  caller_obligation c ω op.
Proof. by rewrite to_hoare_triggerE hoc_pre_condE. Qed.

Lemma to_hoare_ptrigger_postE (op : F A) (ω : Ω) (a : A) (ω' : Ω) :
  post (to_hoare (M:=M) c (ptrigger op))
    ω a ω' <->
  ω' = witness_update c ω op a /\
  callee_obligation c ω op a.
Proof. by rewrite to_hoare_triggerE hoc_post_condE. Qed.

End contract_trigger_helpers.

(** ** Distinguished Effect Views *)

Section ToHoareDistinguishSection.
Context {Fx F G : eff}
    `{F -<? Fx, G -< Fx, Distinguish Fx G F}
    {M : freerMonad Fx} (Ω : Type) (c : contract F Ω)
    {A : Type} (op : G A).

(* Local Notation used to fix the freerMonad used with the to_hoare mapper. *)
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma to_hoare_distinguished_trigger_preI (ω : Ω) :
  pre (c ||> ptrigger op) ω.
Proof.
by rewrite to_hoare_triggerE /hoare_of_contract /gen_caller_obligation
  (@injK_None Fx G F).
Qed.

Lemma to_hoare_distinguished_trigger_postE (ω : Ω) (x : A) (ω' : Ω) :
  post (c ||> ptrigger op) ω x ω' <->
  ω' = ω.
Proof.
by rewrite to_hoare_triggerE /=
  /gen_witness_update /gen_callee_obligation
  (@injK_None Fx G F);
   split=> [[-> _] | ->].
Qed.
End ToHoareDistinguishSection.

Timeout 3 Check to_hoare_distinguished_trigger_preI.

Global Opaque gen_caller_obligation gen_witness_update gen_callee_obligation.
Global Opaque hoare_of_contract.
Global Opaque to_hoare.
