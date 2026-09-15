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
  (forall (X : Type) (cmd : Fx X),
    preserves_invariant invariant (handler _ cmd)) ->
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
Context {Fx F : effect} `{F -<? Fx} (S : Type) (c : contract F S).

Local Open Scope classical_set_scope.

Definition hoare_of_contract : Fx ~~> hoare S :=
  fun U cmd => mk_hoare
    (gen_requirement c ^~ cmd)
    (fun s (x : U) s' => s' = gen_state_update c s cmd x /\
                         gen_promise c s cmd x).

Definition freer_to_hoare {M : freerMonad Fx} : M ~~> hoare S :=
  denote _ hoare_of_contract.

End hoare_of_contract.
Arguments hoare_of_contract : simpl never.
Arguments freer_to_hoare {Fx F _ M S} c {U} : rename, simpl never.

(** A Hoare triple can be interpreted from the program `p`
  * through the contract `c`.
  *)
Notation "c |> p" := (@freer_to_hoare _ _ _ _ c _ _ p)
  (at level 60, no associativity).

Section freer_to_hoare_lemmas.
Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (S : Type) (c : contract F S).

Local Open Scope classical_set_scope.

Lemma pre_ret {U : Type} (u : U) : pre (c |> (Ret u : M _)) = [set: S].
Proof. by rewrite /freer_to_hoare denote_ret. Qed.

Lemma pre_skip : pre (c |> (skip : M _)) = [set: S].
Proof. by rewrite pre_ret. Qed.

Lemma post_ret {U : Type} (u v : U) (s s' : S) :
  post (c |> (Ret u : M _)) s v s' <-> u = v /\ s = s'.
Proof. by rewrite /freer_to_hoare denote_ret. Qed.

Lemma post_skip (s s' : S) (x : unit) :
  post (c |> (skip : M _)) s x s' <-> s = s'.
Proof.
by rewrite /freer_to_hoare/= post_ret; split=> [[]//|<-]; case: x.
Qed.

End freer_to_hoare_lemmas.

Section GenericToHoareSection.
Context {Fx F : effect} `{F -<? Fx} {M : freerMonad Fx}
    (S : Type) (c : contract F S).

Lemma to_hoare_triggerE (a : Type) (cmd : Fx a) :
  (c |> (trigger a cmd : M _)) = hoare_of_contract c cmd.
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

Lemma post_bindmskip s s' u (x : unit) :
  post (c |> p) s u s' -> post (c |> p >> skip) s x s'.
Proof.
move=> tut'; rewrite freer_to_hoare_bindE/=.
by exists u, s'; split => //; rewrite post_skip.
Qed.

End BindFacts.

Section WhenFacts.
Context {U : Type} (p : M U).

Lemma pre_to_hoare_whenP b (s : S) :
  pre (c |> when b p) s <-> if b then pre (c |> p) s else True.
Proof. by case: b => /=; [rewrite pre_bindmskip|rewrite pre_skip]. Qed.

Lemma post_to_hoare_whenP b (s : S) (x : unit) (s' : S) :
  post (c |> when b p) s x s' <->
  if b
  then exists y, post (c |> p) s y s'
  else s' = s.
Proof.
case: x.
case: b => /=; last by rewrite post_skip; split => /esym.
split.
  rewrite freer_to_hoare_bindE/= => -[u' [t2 [H1 H2]]].
  exists u'.
  by move: H2; rewrite post_skip => <-.
move=> [u tut'].
rewrite freer_to_hoare_bindE/=.
exists u, s'; split => //.
by rewrite post_skip.
Qed.

End WhenFacts.

End GenericToHoareSection.

Lemma to_hoare_preserves_invariant {Fx F : effect} `{F -<? Fx}
  {M : inductiveFreerMonad Fx} {S : UU0}
  (invariant : set S) (c : contract F S)
  (handler_preserves : forall (A : UU0) (cmd : Fx A),
    preserves_invariant invariant (hoare_of_contract c cmd)) (A : UU0) (p : M A) :
  preserves_invariant invariant (c |> p).
Proof. exact: denote_preserves_invariant. Qed.

(** ** Trigger Views *)

Section contract_trigger_helpers.
Context {Fx F : effect} `{F -< Fx} {M : freerMonad Fx}
    (S : Type) (c : contract F S) {A : Type}.

Lemma pre_to_hoare_triggerP (cmd : F A) (s : S) :
  pre (c |> (ptrigger cmd : M _)) s <->
  requirement c s cmd.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Lemma post_to_hoare_triggerP (cmd : F A) (s : S) (a : A) (s' : S) :
  post (c |> (ptrigger cmd : M _))
    s a s' <->
  s' = state_update c s cmd a /\
  promise c s cmd a.
Proof. by rewrite to_hoare_triggerE /= provided_calleeP. Qed.

End contract_trigger_helpers.

(* Frame rule machinery *)
Module frame_rule.
Module Export SyntaxFreer.

Inductive fSyntax {F : effect} : Type -> Type :=
| ret : forall A, A -> fSyntax A
| bind : forall B A, fSyntax B -> (B -> fSyntax A) -> fSyntax A
| trigger : forall A, F A -> fSyntax A.

Fixpoint fSem {Fx F : effect} `{F -< Fx} {M : freerMonad Fx} {A}
    (m : @fSyntax F A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => fSem m >>= (fSem \o f)
  | trigger A cmd => ptrigger cmd
  end.

Abbreviation freerSyntax := fSyntax.
Abbreviation frRet := ret.
Abbreviation frBind := bind.
Abbreviation frTrigger := trigger.
Abbreviation freerSem := fSem.
End SyntaxFreer.

(** A witness records that a program uses only one of the two effects. *)
Section split_effects.
Context {Fx F : effect} `{F -< Fx}.
Context {M : freerMonad Fx} {A : UU0}.

Definition providesOnlyF (n : M A) := {m | freerSem (F := F) m = n}.
End split_effects.

Section contract_correspondance.
Context {Fx F G : effect} `{F ;; G -<< Fx} {M : freerMonad Fx}
  {T U : UU0} (cf : contract F T) (cg : contract G T).

Lemma freer_contract_left (m : M U) :
  providesOnlyF (F:=F) m -> (cf -^- cg |> m) = (cf |> m).
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
  congr mk_hoare.
  + by apply/funext=> s; rewrite andPT.
  + by apply/eq3_fun=> s b s'; rewrite andPT.
Qed.

Lemma freer_contract_right (m : M U) :
  providesOnlyF (F:=G) m -> (cf -^- cg |> m) = (cg |> m).
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
  congr mk_hoare.
  + by apply/funext=> s; rewrite andTP.
  + by apply/eq3_fun=> s b s'; rewrite andTP.
Qed.

End contract_correspondance.
Section syntax_inclusion.
Context {Fx F G : effect} `{F -< G} `{G -< Fx}.
Context {M : freerMonad Fx} {A : Type}.

Lemma providesOnlyFT (m : M A) :
  providesOnlyF (F:=F) m -> providesOnlyF (F:=G) m.
Proof.
case=> syntax <-.
elim: syntax=>
    [X x | X Y prefix [prefix' prefixE] suffix IHsuffix | X cmd].
- by exists (frRet x).
- exists (frBind prefix' (fun x=> sval (IHsuffix x))).
  rewrite /= prefixE.
  congr (_ >>= _).
  apply: boolp.funext=> x.
  exact: svalP (IHsuffix x).
- by exists (frTrigger (inj cmd)).
Qed.
End syntax_inclusion.
Section lift_shared_contract.
Context {Fx Fg F G : effect} `{F ;; G -<< Fg} `{Fg -< Fx}.
Context {M : freerMonad Fx} {T U : Type}.
Variables (cf : contract F T) (cg : contract G T).

Lemma freer_contract_prodT (m : M U) :
  ((cf -^- cg : contract Fg T) |> m) =
  ((cf -^- cg : contract Fx T) |> m).
Proof.
rewrite /freer_to_hoare.
congr (denote _ _ U m).
apply: functional_extensionality_dep=> A.
apply: boolp.funext=> cmd.
rewrite /hoare_of_contract /sharedcontractprod /gen_requirement
   /gen_state_update /gen_promise /=.
case: (prj cmd)=> [op|] //=.
congr mk_hoare.
- by apply/funext=> s; apply: propext; tauto.
by apply/eq3_fun=> s x s'; apply: propext; tauto.
Qed.
End lift_shared_contract.

#[export] Hint Extern 0 (providesOnlyF _) =>
  multimatch goal with
  | inner : ?F -< ?Fx |- @providesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (providesOnlyFT (F:=F))]
  | inner : ?F;;?G -<< ?Fx
      |- @providesOnlyF _ ?Fx _ _ _ _ =>
      solve [by apply: (providesOnlyFT (F:=F))
            | by apply: (providesOnlyFT (F:=G))]
  end : core.
End frame_rule.
Export frame_rule.
