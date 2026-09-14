From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssrfun functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import
  mathcomp_extra init effect freer contract hoare hoare_lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Local Open Scope monae_scope.

(******************************************************************************)
(******************************************************************************)

Module SyntaxFreer.

Inductive t {F : effect} : Type -> Type :=
| ret : forall A, A -> t A
| bind : forall B A, t B -> (B -> t A) -> t A
| trigger : forall A, F A -> t A.

Fixpoint sem {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} {A} (m : @t F A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => sem m >>= (sem \o f)
  | trigger A op => ptrigger op
  end.

Module Exports.
Notation freerSyntax := t.
Notation frRet := ret.
Notation frBind := bind.
Notation frTrigger := trigger.
Notation freerSem := sem.
End Exports.
End SyntaxFreer.
Export SyntaxFreer.Exports.

Lemma test_canonical (F : effect) (M : freerMonad F) A (a : F A) (b : A -> M A) :
  ptrigger a >>= b = trigger _ a >>= b.
Proof.
Set Printing All.
Unset Printing All.
by [].
Abort.

Section shared_defs.
Context {Fx F G : effect}.
Context `{F ;; G -<< Fx}.
Context {M : freerMonad Fx} {A : UU0}.

Definition provideLeft_isFreer  (n : M A) := {m | freerSem (F:=F) m = n}.
Definition provideRight_isFreer (n : M A) := {m | freerSem (F:=G) m = n}.
End shared_defs.

Section contract_correspondance.
Context {Fx F G : effect} `{F ;; G -<< Fx} {M : freerMonad Fx}
  {A W : UU0} (cf : contract F W) (cg : contract G W).

Lemma freer_contract_left (m : M A) :
  provideLeft_isFreer (F:=F) m -> (cf -^- cg |> m) = cf |> m.
Proof.
rewrite /to_hoare;
  case=> x; elim: x m=>[{} X x m <-| X Y st0 ih0 st1 ih1 m <- | X op m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=>x do rewrite !compE (ih1 x) //=.
  by rewrite ih0.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /= /gen_witness_update /gen_caller_obligation /gen_callee_obligation.
  rewrite /= injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=>w; rewrite andPT.
  + by apply/eq3_fun=> s b s'; rewrite andPT.
Qed.

Lemma freer_contract_right (m : M A) :
  provideRight_isFreer (G:=G) m ->  (cf -^- cg |> m) = cg |> m.
Proof.
rewrite /to_hoare;
  case=> x; elim: x m=>[{} X x m <-| X Y st0 ih0 st1 ih1 m <- | X op m <-] /=.
- by rewrite !denote_ret.
- rewrite !denote_bind.
  under eq_bind=>x do rewrite !compE (ih1 x) //=.
  by rewrite ih0.
- rewrite !denote_trigger /hoare_of_contract /sharedcontractprod /= /gen_witness_update /gen_caller_obligation /gen_callee_obligation.
  rewrite /= injK_Some injK_None.
  congr mk_hoare.
  + by apply/funext=>w; rewrite andTP.
  + by apply/eq3_fun=> s b s'; rewrite andTP.
Qed.

End contract_correspondance.
