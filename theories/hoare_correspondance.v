From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssrfun functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer contract hoare.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

(* Definition commute (M : monad) (A B : UU0) (m : M A) (n : M B) (C : UU0)
  (f : A -> B -> M C) : Prop :=
m >>= (fun x : A => n >>= [eta f x]) =
n >>= (fun y : B => m >>= f^~ y)
     : forall {M : monad} [A B : UU0],
M A -> M B -> forall [C : UU0], (A -> B -> M C) -> Prop. *)

(* monae: Monadic equational reasoning in Rocq                                *)
(* Copyright (C) 2025 monae authors, license: LGPL-2.1-or-later               *)
Local Open Scope monae_scope.

(******************************************************************************)
(******************************************************************************)

(* Lemma bind_ext_guard {M : failMonad} (A : UU0) (b : bool) (m1 m2 : M A) :
  (b -> m1 = m2) -> guard b >> m1 = guard b >> m2.
Proof. by case: b => [->//|_]; rewrite guardF !bindfailf. Qed. *)

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

(* NB: see also nondetState_isNondet *)
Definition provide_isFreer (n : M A) := {m | freerSem (F:=F) m = n}.
Definition provideLeft_isFreer  (n : M A) := {m | freerSem (F:=F) m = n}.
Definition provideRight_isFreer (n : M A) := {m | freerSem (F:=G) m = n}.

Context {W : UU0} (cf : contract F W) (cg : contract G W) .
Definition proj_inj_is_fine {M' : freerMonad F} (p : M A) (p' : M' A) :=
  (cf |> p) = (cf |> p').

Infix "||>" := (to_hoare (Fx:=Fx) (M:=M)) (at level 40).

Definition left_only_is_shared  (p : M A) :=
(* cf -^- cg |> p = *)
  (sharedcontractprod (Fx:=Fx) cf cg |> p) =
  cf |> p.
Definition right_only_is_shared (p : M A) :=
  (sharedcontractprod (Fx := Fx) cf cg |> p) =
  to_hoare (Fx := Fx) (M := M) cg p.

End shared_defs.

Section contract_correspondance.
Context {Fx F G : effect} `{F ;; G -<< Fx} {M : freerMonad Fx}
  {A W : UU0} (cf : contract F W) (cg : contract G W).

Lemma freer_contract_left (m : M A) :
(* (forall (N: freerMonad F) (n: N), m = n) -> *)
  provideLeft_isFreer (F:=F) m -> left_only_is_shared cf cg m.
Proof.
rewrite /left_only_is_shared /to_hoare;
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
  provideRight_isFreer (G:=G) m -> right_only_is_shared cf cg m.
Proof.
rewrite /right_only_is_shared /to_hoare;
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

(* Lemma liftM2_isNondet A B C (f : A -> B -> C) (ma : M A) (mb : M B) :
  plus_isNondet ma -> plus_isNondet mb -> plus_isNondet (liftM2 f ma mb).
Proof.
move=> [s1 s1_ma] [s2 s2_mb].
exists (ndBind s1 (fun a => ndBind s2 (fun b => ndRet (f a b)))).
by rewrite /= s1_ma /comp /= s2_mb.
Qed.

Lemma guard_isNondet (b : bool) : plus_isNondet (guard b : M _).
Proof.
exists (if b then ndRet tt else @ndFail _).
by case: ifP; rewrite (guardT, guardF).
Qed.

Lemma insert_isNondet A (s : seq A) a : plus_isNondet (@insert M _ a s).
Proof.
elim: s => /= [|h t ih]; first by exists (ndRet [:: a]).
rewrite insertE /=; have [syn synE] := ih.
exists (ndAlt (ndRet [:: a, h & t]) (ndBind syn (fun x => ndRet (h :: x)))).
by rewrite /= synE fmapE.
Qed.

Lemma splits_isNondet A (s : seq A) : plus_isNondet (splits s : M _).
Proof.
elim: s => [|h t ih /=]; first by exists (ndRet ([::], [::])).
have [syn syn_splits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt (ndRet (h :: a, b)) (ndRet (a, h :: b)))).
by rewrite /= syn_splits; bind_ext => -[].
Qed.

Lemma splits_bseq_isNondet A (s : seq A) : plus_isNondet (splits_bseq s : M _).
Proof.
elim: s => [|h t ih]; first by exists (ndRet ([bseq], [bseq])).
have [syn syn_tsplits] := ih.
exists (ndBind syn (fun '(a, b) => ndAlt
    (ndRet ([bseq of h :: a], widen_bseq (leqnSn _) b))
    (ndRet (widen_bseq (leqnSn _) a, [bseq of h :: b])))).
by rewrite /= syn_tsplits; bind_ext => -[].
Qed.

Lemma qperm_isNondet A (s : seq A) : plus_isNondet (qperm s : M _).
Proof.
have [n sn] := ubnP (size s); elim: n s => // n ih s in sn *.
move: s => [|h t] in sn *; first by exists (ndRet [::]); rewrite qperm_nil.
rewrite qperm_cons splits_bseqE fmapE bindA.
have [syn syn_tsplits] := splits_bseq_isNondet t.
have liftM2_qperm_isNondet (a b : (size t).-bseq A) :
  plus_isNondet (liftM2 (fun x y => x ++ h :: y) (qperm a) (qperm b : M _)).
  apply: liftM2_isNondet => //; apply: ih.
  - by rewrite (leq_ltn_trans (size_bseq a)).
  - by rewrite (leq_ltn_trans (size_bseq b)).
exists (ndBind syn (fun a => sval (liftM2_qperm_isNondet a.1 a.2))).
rewrite /= syn_tsplits; bind_ext => -[a b] /=.
by rewrite bindretf; case: (liftM2_qperm_isNondet _ _).
Qed. *)

(* Arguments plus_commute {M A} m {B} n {C} f.
#[global] Hint Extern 0 (liftM2_isNondet (guard _)) =>
  solve[exact: liftM2_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (guard _)) =>
  solve[exact: guard_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (insert _ _)) =>
  solve[exact: insert_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (splits _)) =>
  solve[exact: splits_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (splits_bseq _)) =>
  solve[exact: splits_bseq_isNondet] : core.
#[global] Hint Extern 0 (plus_isNondet (qperm _)) =>
  solve[exact: qperm_isNondet] : core. *)

(******************************************************************************)
(******************************************************************************)

(* Lemma guard_splits {T A : UU0} (p : pred T) (t : seq T) (f : seq T * seq T -> M A) :
  splits t >>= (fun x => guard (all p t) >> f x) =
  splits t >>= (fun x => guard (all p x.1) >> guard (all p x.2) >> f x).
Proof.
(* rewrite plus_commute. *)
rewrite -plus_commute //.
elim: t => [|h t ih] in p f *; first by rewrite /= !bindretf.
rewrite [LHS]/= guard_and 2!bindA ih /=.
rewrite plus_commute.
2: rewrite //.
rewrite bindA; bind_ext => -[a b] /=.
rewrite !alt_bindDl !bindretf /= !guard_and !bindA !alt_bindDr.
by congr (_ [~] _); rewrite plus_commute.
Qed. *)
