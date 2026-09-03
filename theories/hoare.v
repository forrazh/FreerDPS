(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer contract.

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

Definition hoare_ret {Σ α} (x : α) : hoare Σ α :=
  mk_hoare [set: Σ] (fun s y s' => x = y /\ s = s').

Definition hoare_bind {Σ α β}
    (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
  mk_hoare (fun s => pre h s /\ (forall x s', post h s x s' -> pre (k x) s'))
           (fun s x s'' => exists y s', post h s y s' /\ post (k y) s' x s'').

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
Let ret := @hoare_ret Σ.
Let bind := @hoare_bind Σ.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_ret/=; congr mk_hoare.
- by apply/funext => s/=; apply/propext; split; tauto.
- apply/eq3_fun => s a s''.
  under eq2_exists do rewrite andA.
  by rewrite ex2C ex2_eqr ex_eqr.
Qed.

(* Local Open Scope ssripat_scope. *)

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind /ret /hoare_bind /hoare_ret/=.
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
move=> A B C m f g; rewrite /bind /ret /hoare_bind /hoare_ret/=.
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
                  gen_callee_obligation c ω op x).
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
  to_hoare c (p >>= f) =
  to_hoare c p >>= fun x => to_hoare c (f x).
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
Section SharedBindHelpers.
Context {Fx F G : effect} `{F ;; G -<< Fx}
    {W : Type} (ci : contract F W) (cj : contract G W)
    {M : freerMonad Fx}.

Lemma pre_to_hoare_shared_left_bind {A B : Type}
    (w : W) (op : F A) (k : A -> M B) :
  caller_obligation ci w op ->
  (forall x,
    callee_obligation ci w op x ->
    pre ((sharedcontractprod (Fx := Fx) ci cj) |> k x)
      (witness_update ci w op x)) ->
  pre ((sharedcontractprod (Fx := Fx) ci cj) |>
    (ptrigger op >>= k)) w.
Proof.
move=> caller suffix.
apply/pre_to_hoare_bind=> [| x w'];
  rewrite !to_hoare_triggerE /= ?shared_left_callerP // ?shared_left_calleeP.
by case=> ->; exact: suffix.
Qed.

Lemma pre_to_hoare_shared_right_bind {A B : Type}
    (w : W) (op : G A) (k : A -> M B) :
  caller_obligation cj w op ->
  (forall x,
    callee_obligation cj w op x ->
    pre ((sharedcontractprod (Fx := Fx) ci cj) |> k x)
      (witness_update cj w op x)) ->
  pre ((sharedcontractprod (Fx := Fx) ci cj) |>
    (ptrigger op >>= k)) w.
Proof.
move=> caller suffix.
apply/pre_to_hoare_bind=> [| x w'];
  rewrite !to_hoare_triggerE /= ?shared_right_callerP // ?shared_right_calleeP.
(* rewrite to_hoare_triggerE /= shared_right_calleeP. *)
by case=> ->; exact: suffix.
Qed.

End SharedBindHelpers.

Section SharedLeftProgramHelpers.
Context {Fx F G : effect} `{F ;; G -<< Fx}
    {W : Type} (ci : contract F W) (cj : contract G W)
    {M : freerMonad Fx}.



Definition lift_left_program {A : Type} {Mf : freerMonad F} (p : Mf A) : M A :=
  denote M (fun _ op => ptrigger (Fx := Fx) op) A p.

Lemma pre_to_hoare_shared_leftP {A : Type} (p : M A) (w : W) :
  pre (to_hoare (M := M)
      (sharedcontractprod (Fx := Fx) ci cj) (p)) w ->
  pre (to_hoare (M := M) ci (p)) w /\ pre (to_hoare (M := M) cj (p)) w.
Abort.

Lemma post_to_hoare_shared_leftP {A : Type} (p : freer F A)
    (w : W) (result : A) (w' : W) :
  post (to_hoare (M := M)
      (sharedcontractprod (Fx := Fx) ci cj) (lift_left_program p))
      w result w' <->
  post (to_hoare (M := M) ci (lift_left_program p)) w result w'.
Abort.

End SharedLeftProgramHelpers.

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
  callee_obligation c ω op a.
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
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger (Fx:=H) op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_left_callerP. Qed.

Lemma pre_to_hoare_triggerR
    {A : Type} (op : G A) (ω : Ω) :
  caller_obligation cj ω op ->
  pre (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger (Fx:=H) op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_right_callerP. Qed.

Lemma post_to_hoare_triggerLP
    {A : Type} (op : F A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger (Fx:=H) op)) ω x ω' <->
  ω' = witness_update ci ω op x /\
  callee_obligation ci ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_left_calleeP. Qed.

Lemma post_to_hoare_triggerRP
    {A : Type} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger (Fx:=H) op)) ω x ω' <->
  ω' = witness_update cj ω op x /\
  callee_obligation cj ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_right_calleeP. Qed.



End ToHoareSharedContractSection.


Section ToHoareSharedContractSection.
Context {F G H I : effect} `{F ;; G -<< H} `{H -< I}
    {M : freerMonad I} (Ω : Type) (ci : contract F Ω)
    (cj : contract G Ω).
Check effect.injT I H F .
Goal forall A op, @inj _ _ _ A op = effect.injT I H F _ op.
Proof. by []. Qed.

Lemma pre_to_hoare_trigger_injL
    {A : Type} (op : F A) (ω : Ω) :
  caller_obligation ci ω op ->
  pre (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_left_caller_injP. Qed.

Lemma pre_to_hoare_trigger_injR
    {A : Type} (op : G A) (ω : Ω) :
  caller_obligation cj ω op ->
  pre (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger op)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_right_caller_injP. Qed.

Lemma post_to_hoare_trigger_injLP
    {A : Type} (op : F A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger op)) ω x ω' <->
  ω' = witness_update ci ω op x /\
  callee_obligation ci ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_left_callee_injP. Qed.

Lemma post_to_hoare_trigger_injRP
    {A : Type} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (M:=M)
    (sharedcontractprod (Fx:=H) ci cj) (ptrigger op)) ω x ω' <->
  ω' = witness_update cj ω op x /\
  callee_obligation cj ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_right_callee_injP. Qed.

End ToHoareSharedContractSection.
