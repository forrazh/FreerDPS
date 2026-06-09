(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* From ExtLib Require Import Functor Applicative Monad. *)
From FreerDPS Require Import Interface Impure Contract Hoare.
From monae Require Import preamble hierarchy monad_transformer.
From mathcomp Require Import ssreflect boolp ssrfun.
From HB Require Import structures.

Generalizable All Variables.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Local Open Scope monae_scope. *)

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

Section hoare_monad_transformer.
  Variable (M : monad).

Record hoareT (Σ : Type) (α : Type) : Type :=
  mk_hoareT { pre : M Σ -> Prop
           ; post : M Σ -> α -> M Σ -> Prop
           }.

Arguments mk_hoareT {Σ α} (pre post).
Arguments pre {Σ α} (_ _).
Arguments post {Σ α} (_ _ _).

Definition hoare_pureT {Σ α} (x : α) : hoareT Σ α :=
  mk_hoareT (fun _ => True) (fun m y m' => x = y /\ m = m').


Definition hoare_bindT {Σ α β} (h : hoareT Σ α) (k : α -> hoareT Σ β) : hoareT Σ β :=
  mk_hoareT (fun s => pre h s /\ (forall x s', post h s x s' -> pre (k x) s'))
           (fun s x s'' => exists y s', post h s y s' /\ post (k y) s' x s'').


End hoare_monad_transformer.

(** ** Monad *)
Module hoare_mon.
  Section hm.
    Variables (Σ: UU0) (M : monad).
    
    Let H_ := (hoare Σ).
    Definition HM := (hoareT M Σ).


    Let ret : forall X, X -> HM X := @hoare_pureT M Σ.
    Let bind : forall A B, HM A -> (A -> HM B) -> HM B := @hoare_bindT M Σ.

    Let right_neutral :  BindLaws.right_neutral  bind ret.
    Proof.
      move=>A. rewrite/bind/ret/hoare_bind/hoare_pure/=.
      case=>pr po.
      congr mk_hoareT; apply/boolp.funext=>s. 
      - apply/boolp.propext => /=; tauto.
      apply/boolp.funext=>a;
      apply/boolp.funext=>s'.
      rewrite boolp.propeqE.
      split. case=>a'; case=>s''.
      all: move=>/=H.
      - firstorder congruence.
      by exists a;  exists s'.  
       (* Prop exten *)
    Qed.

(* Local Open Scope ssripat_scope. *)

    Let left_neutral : BindLaws.left_neutral  bind ret.
    Proof.
      move=>A B a f. rewrite/bind/ret/hoare_bind/hoare_pure/=.
      case eFA: (f a).
      congr mk_hoareT; apply/boolp.funext=>s.
      - apply/boolp.propext=>/=; firstorder.
        (* How to specialize ? *)
        + by move: H0 eFA => /(_ a s) /[swap] -> /=; exact.
        + by subst; rewrite eFA.
      - apply/boolp.funext=>b; apply/boolp.funext=>s'.
        rewrite boolp.propeqE. 
      split. 
      - case=>a'; case=>s''.
      all: move=>/=H.
      - firstorder. by rewrite -H-H1 eFA in H0.
      
      exists a;  exists s.
      rewrite eFA/=;
        firstorder.  
    Qed. 

    Let assoc : BindLaws.associative  bind.
    Proof.
      move=>A B C m f g. rewrite/bind/ret/hoare_bind/hoare_pure/=.
      case: m=>prA poA. 
      congr mk_hoareT; apply/boolp.funext=>s.
      - apply/boolp.propext=>/=; firstorder.
        move:x s' x0 s'0 H0  H  H1 H2 H3=>a s' b s'' Hcomb _ _ Hpostm Hpostf.
        case eGB : (g b).
         (* => /=[prC poC]. *)
        move: Hcomb eGB=>/(_ b s'')/[swap]->; apply.
        exists a; exists s'.
        by split.        
      apply/boolp.funext=>c;
        apply/boolp.funext=>s'''.
      apply/boolp.propext=>/=.
      firstorder; 
        move:x x0 x1 x2 H H0 H1=>x s'' y s' HpostA Hpostf Hpostg;
        exists y; 
        exists s'; 
        firstorder.
    Qed.

    HB.instance Definition _ := isMonad_ret_bind.Build HM left_neutral right_neutral assoc.
Definition liftS {S} (A : UU0) (m : M A) : MS S M A :=
  fun s => m >>= (fun x => Ret (x, s)).

  Check liftS.
  Definition lift_pre `(a : A) : M A -> Prop.  Admitted.
    Definition liftH (A : UU0) (m : M A) : HM A := m >>= (fun a => mk_hoareT (lift_pre a) (fun _ _ _=> True)). 
  (* Admitted. *)

  Axiom retliftH : MonadMLaws.ret liftH.
  Axiom bindliftH : MonadMLaws.bind liftH.

  HB.instance Definition _ := isMonadM_ret_bind.Build
  M HM liftH retliftH bindliftH.
     (* := m >>= (fun a => Ret {| pre := _ |}). *)
    (* apply/bind.  *)
    (* - apply m. *)
(* 
Definition liftS (A : UU0) (m : M A) : MS A :=
  fun s => m >>= (fun x => Ret (x, s)).

Let retliftS : MonadMLaws.ret liftS.
Proof.
move=> A; rewrite /liftS; apply: boolp.funext => a /=; apply: boolp.funext => s /=.
by rewrite bindretf.
Qed.

Let bindliftS : MonadMLaws.bind liftS.
Proof.
move=> A B m f; rewrite {1}/liftS; apply: boolp.funext => s.
rewrite [in LHS]bindA.
transitivity (liftS m s >>= uncurry (@liftS B \o f)) => //.
rewrite [in RHS]bindA.
by under [RHS]eq_bind do rewrite bindretf.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build
  M MS liftS retliftS bindliftS. *)

Check MS_mapE.
(* MS_mapE
     : forall (S : UU0) (M : monad) (A B : UU0) (f : A -> B) (m : MS S M A),
([the functor of MS S M] # f) m = M # (fun x : A * S => (f x.1, x.2)) \o  m *)
Check MS.
(* MS
     : UU0 -> monad -> UU0 -> UU0 *)

Check hoareT.
Check hoare.
(* hoare
     : monad -> UU0 -> UU0 -> UU0 *)
Program Definition func  (A B C : UU0) (f : A -> B) (m : M A) : C -> M A := (M # (fun x => x)) \o (fun (c: C) => m) .
Program Definition fun2  (A B C : UU0) (f : A -> B) (m : HM A) : C -> HM A := (M # (fun x:H_ A => {|pre := (fun _ =>True) ; post := fun _ _ _=> True|})) \o (fun (c: C) => m) .

    Lemma HM_mapE (A B : UU0) (f : A -> B) (m : HM A) :
  ([the functor of HM] # f) m = (M # (fun x => f x)) \o m.
Proof.
apply boolp.funext=> s.
rewrite {1}/actm /= /bindS /= fmapE.
congr bind.
by apply: boolp.funext; case.
Qed.

Definition liftS (A : UU0) (m : M A) : MS A :=
  fun s => m >>= (fun x => Ret (x, s)).

Let retliftS : MonadMLaws.ret liftS.
Proof.
move=> A; rewrite /liftS; apply: boolp.funext => a /=; apply: boolp.funext => s /=.
by rewrite bindretf.
Qed.

Let bindliftS : MonadMLaws.bind liftS.
Proof.
move=> A B m f; rewrite {1}/liftS; apply: boolp.funext => s.
rewrite [in LHS]bindA.
transitivity (liftS m s >>= uncurry (@liftS B \o f)) => //.
rewrite [in RHS]bindA.
by under [RHS]eq_bind do rewrite bindretf.
Qed.

HB.instance Definition _ := isMonadM_ret_bind.Build
  M MS liftS retliftS bindliftS.
  End hm.
End hoare_mon.

HB.export hoare_mon.

(** * Reasoning about Programs *)

Definition interface_to_hoare `{MayProvide ix i} `(c : contract i Ω) : ix ~~> hoare Ω :=
  fun a e =>
    {| pre := fun ω => gen_caller_obligation c ω e
     ; post := fun ω x ω' => gen_callee_obligation c ω e x
                             /\ ω' = gen_witness_update c ω e x
    |}.

Definition to_hoare `{MayProvide ix i} {im : impureMonad ix} `(c : contract i Ω)
  : im ~~> hoare Ω :=
  impure_lift _ (interface_to_hoare c).

Arguments to_hoare {ix i _ im Ω} c {α} : rename.
