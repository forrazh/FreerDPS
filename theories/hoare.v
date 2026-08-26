(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer.

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
Definition hoare_ret {Σ α} (x : α) : hoare Σ α :=
  mk_hoare [set: Σ] (fun s y s' => x = y /\ s = s').

Definition hoare_bind {Σ α β}
    (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
(*                                        vv This can be simplified normally *)
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
Let ret := @hoare_ret Σ.
Let bind := @hoare_bind Σ.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_ret/=; congr mk_hoare.
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

Section hlib.
Context {S A B : UU0}.
Lemma hoare_bindE  (h : hoare S A) (k : A -> hoare S B) :
  @bind (hoare S) A B h k = hoare_bind h k.
Proof. by []. Qed.

Definition triple {S A} (P : S -> Prop) (h : hoare S A)
    (Q : A -> S -> Prop) : Prop :=
  forall s, P s ->
    pre h s /\ (forall x s', post h s x s' -> Q x s').
Notation "'[' h ']' '{{' P '}}' '{{' Q '}}'" := (triple P h Q) (at level 0, no associativity).

Lemma triple_weaken_post (h : hoare S A) (P : S -> Prop)
    (Q R : A -> S -> Prop) :
  [h] {{P}} {{Q}} ->
  (forall x s, Q x s -> R x s) ->
  [h] {{P}} {{R}}.
Proof.
move=>+ HQR s Hp=>/(_ s Hp) [Hpre Hpost]; split=>//*.
exact/HQR/Hpost.
Qed.

Lemma triple_strengthen_pre (h : hoare S A) (P R : S -> Prop)
    (Q : A -> S -> Prop) :
  [h] {{P}} {{Q}} ->
  (forall s, R s -> P s) ->
  [h] {{R}} {{Q}}.
Proof. by move=> Hpq + s Hr=> /(_ s Hr); exact: Hpq. Qed.

(* Binary assertions retain a reference state; composition is expanded. *)
Lemma triple_relcomp (h : hoare S A) (P R : S -> S -> Prop)
    (Q : S -> A -> S -> Prop) :
  (forall s, [h] {{P s}} {{Q s}}) ->
  forall s,
    [h] {{fun s' => exists past, R s past /\ P past s'}}
      {{fun x s' => exists past, R s past /\ Q past x s'}}.
Proof.
move=> + s s' [ss] [HR HP]=> /(_ _ _ HP) [Hpre Hpost]; split=>//*.
exists ss; split=>//.
exact: Hpost.
Qed.

Lemma triple_bind (h : hoare S A) (k : A -> hoare S B)
    (P : S -> Prop) (Q : A -> S -> Prop)
    (R : B -> S -> Prop) :
  [h] {{P}} {{Q}} ->
  (forall x, [k x] {{Q x}} {{R}}) ->
  [hoare_bind h k] {{P}} {{R}}.
Proof.
move=> + Kqr s HP=>/(_ s HP) [Hpre Hpost]; split.
- by split=>//a s' Hpp; move: Kqr=>/(_ a s') [] //; exact: Hpost.
- move=> b ss [a] [s'] [Hpp Kpp].
  move: Kqr=> /(_ a s') [].
  + exact: Hpost.
  + by move=> Kpre; exact.
Qed.
End hlib.

Notation "'[' h ']' '{{' P '}}' '{{' Q '}}'" := (triple P h Q) (at level 0, no associativity).

