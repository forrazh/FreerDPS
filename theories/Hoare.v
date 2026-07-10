(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import Init.
(* From ExtLib Require Import Functor Applicative Monad. *)
From FreerDPS Require Import Effect Freer Contract mathcomp_extra.
From mathcomp Require Import all_boot classical_sets.

Generalizable All Variables.

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

(** * Instances *)



(** ** Functor *)

Definition hoare_map {Σ α β} (f : α -> β) (h : hoare Σ α) : hoare Σ β :=
  hoare_bind h (fun x => hoare_pure (f x)).

(** ** Applicative *)

Definition hoare_apply {Σ α β} (hf : hoare Σ (α -> β)) (h : hoare Σ α)
  : hoare Σ β :=
  hoare_bind hf (fun f => hoare_map f h).

(** ** Monad *)

(** A nominal class for monads with Hoare semantics. *)
HB.mixin Record isMonadHoare (S : UU0)
    (M : UU0 -> UU0) of Monad M := {}.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (S : UU0) :=
  {M of isMonadHoare S M &}.

Module hoare_mon.
Section hm.
Variable Σ : UU0.
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

HB.instance Definition _ (S : UU0) :=
  isMonadHoare.Build S (hoare S).

(** ** Primitive Views *)

Lemma hoare_pureE {Σ α} (x : α) :
  @ret (hoare Σ) α x = @hoare_pure Σ α x.
Proof. by []. Qed.

Lemma hoare_bindE {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) :
  @bind (hoare Σ) α β h k = hoare_bind h k.
Proof. by []. Qed.

Lemma hoare_pure_preE {Σ α} (x : α) s :
  pre (@ret (hoare Σ) α x) s <-> True.
Proof. by rewrite hoare_pureE /hoare_pure. Qed.

Lemma hoare_pure_postE {Σ α} (x y : α) s s' :
  post (@ret (hoare Σ) α x) s y s' <-> x = y /\ s = s'.
Proof. by rewrite hoare_pureE /hoare_pure. Qed.

Lemma hoare_bind_preE {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) s :
  pre (h >>= k) s <->
  pre h s /\ (forall x s', post h s x s' -> pre (k x) s').
Proof. by rewrite hoare_bindE /hoare_bind. Qed.

Lemma hoare_bind_postE {Σ α β} (h : hoare Σ α)
    (k : α -> hoare Σ β) s x s'' :
  post (h >>= k) s x s'' <->
  exists y s', post h s y s' /\ post (k y) s' x s''.
Proof. by rewrite hoare_bindE /hoare_bind. Qed.

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
    (invariant : S -> Prop) (h : hoare S A) :=
  forall state result state',
    pre h state ->
    post h state result state' ->
    invariant state ->
    invariant state'.

Lemma preserves_invariant_ret {S A}
    (invariant : S -> Prop) (result : A) :
  preserves_invariant invariant (@ret (hoare S) A result).
Proof.
by move=> state result' state' _ /hoare_pure_postE [_ <-].
Qed.

Lemma preserves_invariant_bind {S A B} (invariant : S -> Prop)
    (h : hoare S A) (k : A -> hoare S B) :
  preserves_invariant invariant h ->
  (forall result, preserves_invariant invariant (k result)) ->
  preserves_invariant invariant (h >>= k).
Proof.
by move=> h_preserves k_preserves state result state'
  /hoare_bind_preE [h_pre k_pre]
  /hoare_bind_postE [x [statex [h_post k_post]]] state_safe;
exact: k_preserves x statex result state'
  (k_pre x statex h_post) k_post
  (h_preserves state x statex h_pre h_post state_safe).
Qed.

(** * Reasoning about Programs *)

Definition hoare_of_contract {Fx : effect} `{MayProvide Fx F}
    `(c : contract F Ω)
    : Fx ~~> hoare Ω :=
  fun a op => mk_hoare
    (gen_caller_obligation c ^~ op)
    (fun ω x ω' => ω' = gen_witness_update c ω op x /\
                  gen_callee_obligation c ω op x).

Definition to_hoare `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω)
    : im ~~> hoare Ω :=
  denote _ (hoare_of_contract c).
Arguments to_hoare {Fx F _ im Ω} c {α} : rename.

Notation "p |= c" := (to_hoare c p) (at level 70).
