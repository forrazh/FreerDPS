(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import boot functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Pre/post specifications and abstract Hoare validity. *)

Local Open Scope classical_set_scope.
Local Open Scope monae_scope.

Record prepost T U : Type := mk_prepost {
  pre : set T ;
  post : T -> U -> set T }.
Arguments mk_prepost {T U} (pre post).
Arguments pre {T U} (_ _).
Arguments post {T U} (_ _ _).

Module Hoare.
Definition prepost_ret {T} {U : UU0} (x : U) : @prepost T U :=
  mk_prepost [set: T] (fun s y s' => (x = y) /\ (s = s')).

Definition prepost_bind {T} {U V}
    (m : prepost T U) (k : U -> prepost T V) : prepost T V := mk_prepost
    (fun s => pre m s /\ (forall x, post m s x `<=` pre (k x)))
    (fun s x s2 => exists y s', post m s y s' /\ post (k y) s' x s2).

Section hm.
Context (T : UU0).
Let ret := @prepost_ret T.
Let bind := @prepost_bind T.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /prepost_bind /prepost_ret/=; congr mk_prepost.
- by apply/seteqP; split => // s [].
- apply/eq3_fun => s a s''.
  under eq2_exists do rewrite andA.
  by rewrite ex2C ex2_eqr ex_eqr.
Qed.

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind /ret /prepost_bind /prepost_ret/=.
move fa : (f a) => [pr po]; congr mk_prepost.
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
move=> A B C m f g; rewrite /bind /ret /prepost_bind /prepost_ret/=.
case: m => prA poA/=; congr mk_prepost.
- apply/funext=> s; apply/propext; split.
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

HB.instance Definition _ := isMonad_ret_bind.Build (prepost T)
  left_neutral right_neutral assoc.

End hm.

End Hoare.

HB.export Hoare.

HB.about prepost.

HB.mixin Record isMonadHoare
(T : UU0) (N : monad)
(ST : stateRunMonad T N)
  (M : Type -> Type) of Monad M := {
  valid_prepost : forall U : UU0, M U -> ST U -> Prop ;
  valid_ret : forall (U : UU0) (x : U),
    valid_prepost U (Ret x) (Ret x) ;
  valid_bind : forall (U V : UU0) (h : M U) (m : ST U)
      (h' : U -> M V) (k : U -> ST V),
    valid_prepost U h m ->
    (forall x, valid_prepost V (h' x) (k x)) ->
    valid_prepost V (h >>= h') (m >>= k)
}.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (T : UU0) (N : monad) (ST : stateRunMonad T N) :=
  {M of isMonadHoare T N ST M & isMonad M & isFunctor M}.

Arguments valid_prepost {T N ST M U} _ _ : rename.

Notation "{{ pre }} prog {{ post }}" :=
  (valid_prepost (mk_prepost pre post) prog)
  (at level 0,
   format "'[' {{  pre  }} '/ ' prog '/ ' {{  post  }} ']'").

From monae Require Import monad_model monad_transformer.

Module HoareModel.
Section vld_s.
Context {T : UU0}.
Abbreviation HT := (prepost T).
Abbreviation ST := (stateT T option_monad).
(* Context {N : monad} {ST : stateRunMonad T N}. *)
Definition valid {U : UU0} (h : HT U) (m : ST U) : Prop :=
  forall s, pre h s ->
    (forall a s', runStateT m s = Ret (a, s') -> post h s a s').

Lemma valid_ret : forall U (x : U), valid (prepost_ret x) (Ret x) .
Proof. by move=> U u t /= P u' t'; rewrite runStateTret; case. Qed.

Lemma valid_bind : forall U V (h : HT U) (m : ST U)
  (h' : U -> HT V) (k : U -> ST V),
valid h m -> (forall x, valid (h' x) (k x)) -> valid (prepost_bind h h') (m >>= k).
Proof.
move=> U V h m h' k valid_m valid_k s [Hpr Hpo] v t''.
rewrite runStateTbind.
case run_m: runStateT=> [[] | [u t]] //= H.
exists u, t; split.
- exact: valid_m.
- apply: valid_k.
  + by have := valid_m s Hpr u t run_m; exact: Hpo.
  + exact: H.
Qed.

HB.about isMonadHoare.Build.
HB.about prepost.
HB.instance Definition _ := isMonadHoare.Build T option_monad ST HT valid_ret valid_bind.

End vld_s.
End HoareModel.

Definition wp {T U : UU0} (h : prepost T U) (Q : U -> set T) : set T :=
  fun s => pre h s /\ forall x s', post h s x s' -> Q x s'.

Section weakest_preconditions.
Context {T U V : UU0}.

Lemma wp_intro (h : prepost T U) (Q : U -> set T) s
    (pre_h : pre h s)
    (post_Q : forall x s', post h s x s' -> Q x s') :
  wp h Q s.
Proof. by []. Qed.

Lemma wp_pre (h : prepost T U) (Q : U -> set T) s :
  wp h Q s -> pre h s.

Admitted.

Lemma wp_post (h : prepost T U) (Q : U -> set T) s x s' :
  wp h Q s -> post h s x s' -> Q x s'.
Admitted.

Lemma wp_weaken (h : prepost T U) (Q Q' : U -> set T) s :
  wp h Q s ->
  (forall x s', Q x s' -> Q' x s') ->
  wp h Q' s.
Admitted.

Lemma wp_prepost_ret (x : U) (Q : U -> set T) s :
  wp (prepost_ret x) Q s <-> Q x s.
Admitted.

Lemma wp_prepost_bind (h : prepost T U) (k : U -> prepost T V)
    (Q : V -> set T) s :
  wp (prepost_bind h k) Q s <->
  wp h (fun x s' => wp (k x) Q s') s.
Admitted.

Lemma wp_ret (x : U) (Q : U -> set T) s :
  wp (Ret x : prepost T U) Q s <-> Q x s.
Admitted.

Lemma wp_bind (h : prepost T U) (k : U -> prepost T V)
    (Q : V -> set T) s :
  wp (h >>= k) Q s <-> wp h (fun x s' => wp (k x) Q s') s.
Admitted.

End weakest_preconditions.
