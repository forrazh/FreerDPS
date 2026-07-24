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
by move=> state result' state' _; rewrite hoare_pureE=> -[_ <-].
Qed.

Lemma preserves_invariant_bind {S A B} (invariant : S -> Prop)
    (h : hoare S A) (k : A -> hoare S B) :
  preserves_invariant invariant h ->
  (forall result, preserves_invariant invariant (k result)) ->
  preserves_invariant invariant (h >>= k).
Proof.
move=> h_preserves k_preserves state result state';
  rewrite hoare_bindE=> -[h_pre k_pre] [x [statex [h_post k_post]]] state_safe.
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

(* --------------------------------- Facts ---------------------------------- *)

Section GenericToHoareSection.
Variable Fx : effect.
Context `{MayProvide Fx F} {im : freerMonad Fx} `(c : contract F Ω).

Lemma to_hoare_requestE `(op : Fx a) :
  to_hoare (im:=im) c (request a op) = hoare_of_contract c op.
Proof. exact: denote_request. Qed.

Lemma to_hoare_skip_preI (ω : Ω) :
  pre ((skip : im unit) |= c) ω.
Proof. by rewrite /to_hoare denote_ret. Qed.

Section BindFacts.
Context `(p : im a) `(f : a -> im b).

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
Context `(p : im a) (guard : bool).

Lemma to_hoare_when_preE (ω : Ω) :
  pre (when guard p |= c) ω <->
  if guard then pre (p |= c) ω else True.
Proof.
by case: guard=> /=;
  [rewrite to_hoare_bindE; split=> [[ ] | ] //|];
  split=> // *; exact: to_hoare_skip_preI.
Qed.

Lemma to_hoare_when_postE (ω : Ω) (x : unit) (ω' : Ω) :
  post (when guard p |= c) ω x ω' <->
  if guard
  then exists y, post (p |= c) ω y ω'
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

Section ToHoareDistinguishSection.
Context {Fx F G : effect}
    `{MayProvide Fx F, Provide Fx G, Distinguish Fx G F}
    {im : freerMonad Fx} `(c : contract F Ω)
    {A} (op : G A).

Local Notation "p ||= c" := (to_hoare (im:=im) c p) (at level 70).

Lemma to_hoare_distinguished_request_preI
     (ω : Ω) :
  pre (trigger op ||= c) ω.
Proof.
by rewrite to_hoare_requestE /hoare_of_contract
  /gen_caller_obligation (@distinguish Fx G F).
Qed.

Lemma to_hoare_distinguished_request_postE
  (ω : Ω) (x : A) (ω' : Ω) :
  post (trigger op ||= c) ω x ω' <->
  ω' = ω.
Proof.
by rewrite to_hoare_requestE /=
  /gen_witness_update /gen_callee_obligation
  (@distinguish Fx G F);
   split=> [[-> _] | ->].
Qed.
End ToHoareDistinguishSection.

Module ToHoareFreerBridge.
(* Bridging lemma. Should ALWAYS be used carefully. *)
Lemma to_hoare_reifyE `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω) `(p : im A) :
  to_hoare (im:=freer Fx) c
    (denote (freer Fx) (@request Fx (freer Fx)) A p)
  = to_hoare (im:=im) c p.
Proof.
by rewrite /to_hoare;
  apply: (denote_unique (hoare Ω) (hoare_of_contract c)
    (fun X => denote _ _ X \o denote _ _ X))=> *;
  rewrite compE ?denote_ret ?denote_bind ?denote_request.
Qed.
End ToHoareFreerBridge.
