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

(* model *)
Module Hoare.

Record hoare (T U : Type) : Type := mk_hoare {
  pre : set T ;
  post : T -> U -> set T }.

Arguments mk_hoare {T U} (pre post).
Arguments pre {T U} (_ _).
Arguments post {T U} (_ _ _).

Definition hoare_ret {Σ α} (x : α) : hoare Σ α :=
  mk_hoare [set: Σ] (fun s y s' => x = y /\ s = s').

Local Open Scope classical_set_scope.

Definition hoare_bind {Σ α β}
    (m : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
  mk_hoare (fun s => pre m s /\ (forall x, post m s x `<=` pre (k x)))
           (fun s x s2 => exists y s', post m s y s' /\ post (k y) s' x s2).

Section hm.
Variable Σ : Type.
Let ret := @hoare_ret Σ.
Let bind := @hoare_bind Σ.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_ret/=; congr mk_hoare.
- by apply/seteqP; split => // s [].
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

End Hoare.

(** ** Monad *)

(** Easier to had future laws from there. *)
(*
HB.mixin Record isMonadHoare (S : Type)
    (M : Type -> Type) of Monad M := {}.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (S : Type) :=
  {M of isMonadHoare S M &}.
*)


HB.export Hoare.

(*HB.instance Definition _ (S : Type) :=
  isMonadHoare.Build S (hoare S).*)

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

Section hoare_of_contract.
Context {Fx F : effect} `{F -<? Fx} (T : Type) (c : contract F T).

Local Open Scope classical_set_scope.

Definition hoare_of_contract : Fx ~~> hoare T :=
  fun U cmd => mk_hoare
    (gen_requirement c ^~ cmd)
    (fun t (x : U) t' => t' = gen_state_update c t cmd x /\
                         gen_promise c t cmd x).

Definition freer_to_hoare {M : freerMonad Fx} : M ~~> hoare T :=
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
