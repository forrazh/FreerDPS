(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer contract hoare.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Invariant Preservation *)

Definition preserves_invariant {S A}
    (invariant : set S) (h : prepost S A) :=
  forall state result state',
    pre h state ->
    post h state result state' ->
    invariant state ->
    invariant state'.

Lemma preserves_invariant_ret {S A}
    (invariant : set S) (result : A) :
  preserves_invariant invariant (@ret (prepost S) A result).
Proof. by move=>???? [_ <-]. Qed.

Lemma preserves_invariant_bind {S A B} (invariant : set S)
    (h : prepost S A) (k : A -> prepost S B) :
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
  {S : UU0} (invariant : set S) (handler : Fx ~~> prepost S) (A : UU0) (p : M A) :
  (forall (X : Type) (op : Fx X),
    preserves_invariant invariant (handler _ op)) ->
  preserves_invariant invariant
    (denote (prepost S) handler A p).
Proof.
move=> H s a s'.
apply: (@denote_ind _ _ _ _  (fun X => preserves_invariant invariant)).
- move=> X x.
  exact: preserves_invariant_ret.
- move=> X Y h k h_preserves k_preserves.
  exact: preserves_invariant_bind h_preserves k_preserves.
- exact: H.
Qed.

Section hoare_of_contract.
Context {Fx F : effect} `{F -<? Fx} (T : Type) (c : contract F T).

Local Open Scope classical_set_scope.

Definition hoare_of_contract : Fx ~~> prepost T :=
  fun U cmd => mk_prepost
    (gen_requirement c ^~ cmd)
    (fun t (x : U) t' => t' = gen_state_update c t cmd x /\
                         gen_promise c t cmd x).

Definition freer_to_hoare {M : freerMonad Fx} : M ~~> prepost T :=
  denote _ hoare_of_contract.

End hoare_of_contract.
Arguments hoare_of_contract : simpl never.
Arguments freer_to_hoare {Fx F _ M Ω} c {α} : rename, simpl never.

(** A Hoare triple can be interpreted from the program `p`
  * through the contract `c`.
  *)
Notation "c |> p" := (@freer_to_hoare _ _ _ _ c _ _ p)
  (at level 60, no associativity).

Section freer_to_hoare_lemmas.
Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (T : Type) (c : contract F T).

Local Open Scope classical_set_scope.

Lemma pre_ret {U : Type} (u : U) : pre (c |> (Ret u : M _)) = [set: T].
Proof. by rewrite /freer_to_hoare denote_ret. Qed.

Lemma pre_skip : pre (c |> (skip : M _)) = [set: T].
Proof. by rewrite pre_ret. Qed.

Lemma post_ret {U : Type} (u v : U) (t t' : T) :
  post (c |> (Ret u : M _)) t v t' <-> u = v /\ t = t'.
Proof. by rewrite /freer_to_hoare denote_ret. Qed.

Lemma post_skip (t t' : T) (x : unit) :
  post (c |> (skip : M _)) t x t' <-> t = t'.
Proof.
by rewrite /freer_to_hoare/= post_ret; split=> [[]//|<-]; case: x.
Qed.

End freer_to_hoare_lemmas.

Section GenericToHoareSection.
Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (T : Type) (c : contract F T).

Lemma to_hoare_triggerE (a : Type) (op : Fx a) :
  (c |> (trigger a op : M _)) = hoare_of_contract c op.
Proof. exact: denote_trigger. Qed.

Lemma freer_to_hoare_bindE {a b : Type} (p : M a) (f : a -> M b) :
  c |> (p >>= f) = (c |> p) >>= fun x => (c |> (f x)).
Proof. exact: denote_bind. Qed.

Section BindFacts.
Context {A B : Type} (p : M A) (f : A -> M B).

Lemma pre_bindmskip : pre (c |> p >> skip) = pre (c |> p).
Proof.
apply/funext => s; rewrite freer_to_hoare_bindE.
apply/propext; split=> [[]//|cps/=]; split => //.
by rewrite pre_skip.
Qed.

Lemma post_bindmskip t t' u (x : unit) :
  post (c |> p) t u t' -> post (c |> p >> skip) t x t'.
Proof.
move=> tut'; rewrite freer_to_hoare_bindE/=.
by exists u, t'; split => //; rewrite post_skip.
Qed.

End BindFacts.

Section WhenFacts.
Context {U : Type} (p : M U).

Lemma pre_to_hoare_whenP b (t : T) :
  pre (c |> when b p) t <-> if b then pre (c |> p) t else True.
Proof. by case: b => /=; [rewrite pre_bindmskip|rewrite pre_skip]. Qed.

Lemma post_to_hoare_whenP b (t : T) (x : unit) (t' : T) :
  post (c |> when b p) t x t' <->
  if b
  then exists y, post (c |> p) t y t'
  else t' = t.
Proof.
case: x.
case: b => /=; last by rewrite post_skip; split => /esym.
split.
  rewrite freer_to_hoare_bindE/= => -[u' [t2 [H1 H2]]].
  exists u'.
  by move: H2; rewrite post_skip => <-.
move=> [u tut'].
rewrite freer_to_hoare_bindE/=.
exists u, t'; split => //.
by rewrite post_skip.
Qed.

End WhenFacts.

End GenericToHoareSection.

Section SharedBindHelpers.
Context {Fx F G : effect} `{F ;; G -<< Fx}
    {W : Type} (ci : contract F W) (cj : contract G W)
    {M : freerMonad Fx}.

Lemma pre_to_hoare_shared_left_bind {A B : Type}
    (w : W) (op : F A) (k : A -> M B) :
  requirement ci w op ->
  (forall x,
    promise ci w op x ->
    pre ((sharedcontractprod (Fx := Fx) ci cj) |> k x)
      (state_update ci w op x)) ->
  pre ((sharedcontractprod (Fx := Fx) ci cj) |>
    (ptrigger op >>= k)) w.
Proof.
move=> caller suffix.
rewrite freer_to_hoare_bindE/=; split.
  rewrite to_hoare_triggerE /=.
  by rewrite shared_left_callerP.
move=> a.
rewrite to_hoare_triggerE /= => w'.
rewrite shared_left_calleeP => -[-> ?].
exact: suffix.
Qed.

Lemma pre_to_hoare_shared_right_bind {A B : Type}
    (w : W) (op : G A) (k : A -> M B) :
  requirement cj w op ->
  (forall x,
    promise cj w op x ->
    pre ((sharedcontractprod (Fx := Fx) ci cj) |> k x)
      (state_update cj w op x)) ->
  pre ((sharedcontractprod (Fx := Fx) ci cj) |>
    (ptrigger op >>= k)) w.
Proof.
move=> caller suffix.
rewrite freer_to_hoare_bindE/=; split.
  rewrite to_hoare_triggerE /=.
  by rewrite shared_right_callerP.
move=> a.
rewrite to_hoare_triggerE /= => w'.
rewrite shared_right_calleeP => -[-> ?].
exact: suffix.
Qed.

End SharedBindHelpers.

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
  pre (c |> (ptrigger op : M _)) ω <->
  requirement c ω op.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Lemma post_to_hoare_triggerP (op : F A) (ω : Ω) (a : A) (ω' : Ω) :
  post (c |> (ptrigger op : M _))
    ω a ω' <->
  ω' = state_update c ω op a /\
  promise c ω op a.
Proof. by rewrite to_hoare_triggerE /= provided_calleeP. Qed.

End contract_trigger_helpers.

(** ** Shared Contract Trigger Views *)

Section ToHoareSharedContractSection.
Context {F G H : effect} `{F ;; G -<< H}
    {M : freerMonad H} (Ω : Type) (ci : contract F Ω)
    (cj : contract G Ω).

Lemma pre_to_hoare_triggerL
    {A : Type} (op : F A) (ω : Ω) :
  requirement ci ω op ->
  pre (ci -^- cj |> (ptrigger op : M _)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_left_callerP. Qed.

Lemma pre_to_hoare_triggerR
    {A : Type} (op : G A) (ω : Ω) :
  requirement cj ω op ->
  pre ((ci -^- cj) |> (ptrigger op : M _)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_right_callerP. Qed.

Lemma post_to_hoare_triggerLP
    {A : Type} (op : F A) (ω : Ω) (x : A) (ω' : Ω) :
  post (ci -^- cj |> (ptrigger op : M _)) ω x ω' <->
  ω' = state_update ci ω op x /\
  promise ci ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_left_calleeP. Qed.

Lemma post_to_hoare_triggerRP
    {A : Type} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post (ci -^- cj |> (ptrigger op : M _)) ω x ω' <->
  ω' = state_update cj ω op x /\
  promise cj ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_right_calleeP. Qed.
End ToHoareSharedContractSection.


Section ToHoareSharedContractSection.
Context {F G H I : effect} `{F ;; G -<< H} `{H -< I}
    {M : freerMonad I} (Ω : Type) (ci : contract F Ω)
    (cj : contract G Ω).

Lemma pre_to_hoare_trigger_injL
    {A : Type} (op : F A) (ω : Ω) :
  requirement ci ω op ->
  pre (ci -^- cj |> (ptrigger op : M _)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_left_caller_injP. Qed.

Lemma pre_to_hoare_trigger_injR
    {A : Type} (op : G A) (ω : Ω) :
  requirement cj ω op ->
  pre ((ci -^- cj) |> (ptrigger op : M _)) ω.
Proof. by rewrite to_hoare_triggerE /= shared_right_caller_injP. Qed.

Lemma post_to_hoare_trigger_injLP
    {A : Type} (op : F A) (ω : Ω) (x : A) (ω' : Ω) :
  post ((ci -^- cj) |> (ptrigger op : M _)) ω x ω' <->
  ω' = state_update ci ω op x /\
  promise ci ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_left_callee_injP. Qed.

Lemma post_to_hoare_trigger_injRP
    {A : Type} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post ((ci -^- cj) |> (ptrigger op : M _)) ω x ω' <->
  ω' = state_update cj ω op x /\
  promise cj ω op x.
Proof. by rewrite to_hoare_triggerE /= shared_right_callee_injP. Qed.

End ToHoareSharedContractSection.

(* Frame rule machinery *)
Module frame_rule.
Module Export SyntaxFreer.

Inductive fSyntax {F : effect} : Type -> Type :=
| ret : forall A, A -> fSyntax A
| bind : forall B A, fSyntax B -> (B -> fSyntax A) -> fSyntax A
| trigger : forall A, F A -> fSyntax A.

Fixpoint sem {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} {A}
    (m : @fSyntax F A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => sem m >>= (sem \o f)
  | trigger A cmd => ptrigger cmd
  end.

Abbreviation freerSyntax := fSyntax.
Abbreviation frRet := ret.
Abbreviation frBind := bind.
Abbreviation frTrigger := trigger.
Abbreviation freerSem := sem.
End SyntaxFreer.

(** A witness records that a program uses only one of the two effects. *)
Section split_effects.
Context {Fx F G : effect} `{F ;; G -<< Fx}.
Context {M : freerMonad Fx} {A : UU0}.

Definition provideLeft_isFreer (n : M A) := {m | freerSem (F := F) m = n}.
Definition provideRight_isFreer (n : M A) := {m | freerSem (F := G) m = n}.
End split_effects.

Section contract_correspondance.
Context {Fx F G : effect} `{F ;; G -<< Fx} {M : freerMonad Fx}
  {T U : UU0} (cf : contract F T) (cg : contract G T).

Lemma freer_contract_left (m : M U) :
  provideLeft_isFreer m -> (cf -^- cg |> m) = (cf |> m).
Proof.
rewrite /freer_to_hoare.
case=> syntax; elim: syntax m=>
    [X x m <- | X Y prefix IHprefix suffix IHsuffix m <- | X cmd m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_prepost.
  + by apply/funext=> s; rewrite andPT.
  + by apply/eq3_fun=> s b s'; rewrite andPT.
Qed.

Lemma freer_contract_right (m : M U) :
  provideRight_isFreer m -> (cf -^- cg |> m) = (cg |> m).
Proof.
rewrite /freer_to_hoare.
case=> syntax; elim: syntax m=>
    [X x m <- | X Y prefix IHprefix suffix IHsuffix m <- | X cmd m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=> x do rewrite !compE (IHsuffix x) //=.
  by rewrite IHprefix.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /=.
  rewrite /gen_state_update /gen_requirement /gen_promise /=.
  rewrite injK_Some injK_None.
  congr mk_prepost.
  + by apply/funext=> s; rewrite andTP.
  + by apply/eq3_fun=> s b s'; rewrite andTP.
Qed.

End contract_correspondance.
End frame_rule.

Export frame_rule.
