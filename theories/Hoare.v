(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* From ExtLib Require Import Functor Applicative Monad. *)
From HB Require Import structures.
From FreerDPS Require Import Interface Impure Contract.
From mathcomp Require Import all_boot boolp classical_sets.
From monae Require Import preamble hierarchy.

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

Definition hoare_bind {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
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

(* TODO: move to MCA *)
Lemma ex3_exchangeC A B C (P : A -> B -> C -> Prop) :
  (exists a b c, P a b c) = (exists c b a, P a b c).
Proof.
by apply/propeqP; split=> -[x [y [z xyz]]]; [exists z, y, x|exists z, y, x].
Qed.

Lemma ex3_exchangeAC A B C (P : A -> B -> C -> Prop) :
  (exists a b c, P a b c) = (exists a c b, P a b c).
Proof.
apply/propeqP; split => [[a [b [c abc]]]|[a [c [b abc]]]].
  by exists a, c, b.
by exists a, b, c.
Qed.

Lemma ex_andl A (P : A -> Prop) (Q : Prop) :
  (exists a, P a /\ Q) = ((exists a, P a) /\ Q).
Proof.
apply/propeqP; split=> [[a [Pa q]]|[[a Pa] q]].
  by split => //; exists a.
by exists a.
Qed.

Lemma ex_andr A (P : Prop) (Q : A -> Prop) :
  (exists a, P /\ Q a) = (P /\ (exists a, Q a)).
Proof.
under eq_exists do rewrite andC.
by rewrite ex_andl andC.
Qed.

Lemma eq4_exists T S R N
  (U V : forall (x : T) (y : S x) (z : R x y), N x y z -> Prop) :
  (forall x y z n, U x y z n = V x y z n) ->
  (exists x y z n, U x y z n) = (exists x y z n, V x y z n).
Proof. by move=> UV; apply/eq3_exists => x y z; exact/eq_exists. Qed.
(* /TODO: move to MCA *)

(** ** Monad *)
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
  apply/propext; split => [[a' [s' [_ [<- <-]]]]//|sas''].
  by exists a, s''.
Qed.

(* Local Open Scope ssripat_scope. *)

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f.
rewrite /bind /ret /hoare_bind /hoare_pure/=.
move fa : (f a) => [pr po]; congr mk_hoare.
- apply/funext=> s; apply/propext; split=> [[_]|].
  + by move=> /(_ a s); rewrite fa/=; exact.
  + by move=> prs; split => // _ _ [<- <-]; rewrite fa.
- apply/eq3_fun => s b s'.
  apply/propext; split => [[_ [_ [[<- <-]]]]|sbs'].
  + by rewrite fa.
  + by exists a, s; rewrite fa.
Qed.

Let assoc : BindLaws.associative bind.
Proof.
move=> A B C m f g.
rewrite /bind /ret /hoare_bind /hoare_pure/=.
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
  rewrite ex3_exchangeC.
  apply: eq_exists => a.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3_exchangeC.
  apply: eq_exists => s2.
  rewrite -ex_andr.
  under [in RHS]eq_exists do rewrite -ex_andr.
  by under [in RHS]eq2_exists do rewrite andA.
Qed.

HB.instance Definition _ := isMonad_ret_bind.Build (hoare Σ)
  left_neutral right_neutral assoc.

End hm.
End hoare_mon.

HB.export hoare_mon.

(** * Reasoning about Programs *)

Definition interface_to_hoare `{MayProvide ix i} `(c : contract i Ω)
    : ix ~~> hoare Ω :=
  fun a e => mk_hoare
    (fun ω => gen_caller_obligation c ω e)
    (fun ω x ω' => gen_callee_obligation c ω e x /\
                   ω' = gen_witness_update c ω e x).

Definition to_hoare `{MayProvide ix i} {im : impureMonad ix} `(c : contract i Ω)
    : im ~~> hoare Ω :=
  impure_lift _ (interface_to_hoare c).
Arguments to_hoare {ix i _ im Ω} c {α} : rename.
