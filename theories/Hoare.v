(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* From ExtLib Require Import Functor Applicative Monad. *)
From FreerDPS Require Import Interface Impure Contract.
From monae Require Import preamble hierarchy.
From mathcomp Require Import ssreflect.
From HB Require Import structures.

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

Record hoare (Σ : Type) (α : Type) : Type :=
  mk_hoare { pre : Σ -> Prop
           ; post : Σ -> α -> Σ -> Prop
           }.

Arguments mk_hoare {Σ α} (pre post).
Arguments pre {Σ α} (_ _).
Arguments post {Σ α} (_ _ _).

Definition hoare_pure {Σ α} (x : α) : hoare Σ α :=
  mk_hoare (fun _ => True) (fun s y s' => x = y /\ s = s').

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

(** ** Monad *)
Module hoare_mon.
  Section hm.
    Variable Σ: UU0.
    Let ret := @hoare_pure Σ.
    Let bind := @hoare_bind Σ.

    Let right_neutral :  BindLaws.right_neutral  bind ret.
    Proof.
      move=>A. rewrite/bind/ret/hoare_bind/hoare_pure/=.
      case=>pr po.
      congr mk_hoare; apply/boolp.funext=>s. 
      - apply/boolp.propext; tauto.
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
      congr mk_hoare; apply/boolp.funext=>s.
      - apply/boolp.propext=>/=; firstorder.
        (* How to specialize ? *)
        + by move: H0 eFA => /(_ a s) /[swap]  -> /=; exact.
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
      congr mk_hoare; apply/boolp.funext=>s.
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

    HB.instance Definition _ := isMonad_ret_bind.Build (hoare Σ) left_neutral right_neutral assoc.

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
