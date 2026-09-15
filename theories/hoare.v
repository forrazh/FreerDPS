(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import all_boot functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** To reason about impure computations, we introduce the “Hoare
    monad,” also called the “specification monad.” An instance of the
    specification monad is a couple of [pre] and [post] conditions,
    such that [pre p T] means the program specified by [p] can be
    executed safely from a state [T], and [post p T x T'] means the
    execution of [p] from [T] may compute a result [x] and bring the
    system to a state [T'].

    We equip this couple of predicate with a [bind] function to
    sequentially compose specifications. *)

Local Open Scope classical_set_scope.

(* model *)
Module Hoare.

Record hoare (T U : Type) : Type := mk_hoare {
  pre : set T ;
  post : T -> U -> set T }.

Arguments mk_hoare {T U} (pre post).
Arguments pre {T U} (_ _).
Arguments post {T U} (_ _ _).

Definition hoare_ret {T U} (x : U) : hoare T U :=
  mk_hoare [set: T] (fun s y s' => (x = y) /\ (s = s')).

Definition hoare_bind {T U V}
    (m : hoare T U) (k : U -> hoare T V) : hoare T V :=
  mk_hoare (fun s => pre m s /\ (forall x, post m s x `<=` pre (k x)))
           (fun s x s2 => exists y s', post m s y s' /\ post (k y) s' x s2).

Section hm.
Variable T : Type.
Let ret := @hoare_ret T.
Let bind := @hoare_bind T.

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

HB.instance Definition _ := isMonad_ret_bind.Build (hoare T)
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
