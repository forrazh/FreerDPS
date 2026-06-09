(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on interfaces, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From Stdlib Require Import Setoid Morphisms.
(* From ExtLib Require Import StateMonad MonadState MonadTrans. *)
From FreerDPS Require Import Interface Impure Semantics Component.
From mathcomp Require Import ssreflect.
From monae Require Import preamble hierarchy.
#[local]
Open Scope signature_scope.
Open Scope monae_scope.

Generalizable All Variables.

(** * Definition *)

(** A contract_m dedicated to [i : interface] primarily provides two
    predicates.

    - [caller_obligation] distinguishes between primitives that can be used (by
      an impure computation), and primitives that cannot be used.
    - [callee_obligation] specifies which guarantees can be expected from
      primitives results, as computed by a “good” operational semantics.

    Both [caller_obligation] and [callee_obligation] model properties that may
    vary in time, e.g., a primitive may be forbidden at a given time, but
    authorized later.  To take this possibility into account, contracts are
    parameterized by what we have called a “witness.”  A witness is a term which
    describes the necessary information of the past, and allows for taking
    decision for the present.  It can be seen as an abstraction of the concrete
    state of the interface implementor.

    To keep this state up-to-date after each primitive interpretation,
    contracts also define a dedicated function [witness_update]. *)
Record contract_m (i : interface) (M : monad) (Ω : UU0) : UU0 :=
  make_contract_m
  { witness_update :
      Ω -> forall α, i α -> M α -> forall b, M b

  ; caller_obligation :
      Ω -> forall α, i α -> Prop

  ; callee_obligation :
      Ω -> forall α, i α -> M α -> Prop
  }.

  Declare Scope contract_scope.
Bind Scope contract_scope with contract_m.

Arguments make_contract_m [i M Ω] (_ _ _).
Check witness_update _ _ _ _.
Arguments witness_update [i M Ω] (c ω) [α] (_ _).
Arguments caller_obligation [i M Ω] (c ω) [α] (_).
Arguments callee_obligation [i M Ω] (c ω) [α] (_ _).

(* ========================================================================= *)
Section s_contract.
  Context {M : monad}. 
  Definition const_witness {i} ()  := fun (_ : unit) a (e : i a) (m : M a) b => @skip M.

Inductive no_caller_obligation {i} {Ω} (ω : Ω) (α : Type) (e : i α) : Prop :=
| mk_no_caller_obligation : no_caller_obligation ω α e.

Hint Constructors no_caller_obligation : freespec.

Inductive no_callee_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) (x : M α) : Prop :=
| mk_no_callee_obligation : no_callee_obligation ω α e x.

Hint Constructors no_callee_obligation : freespec.

Definition no_contract (i : interface) : contract_m i M unit :=
  {| witness_update := const_witness
   ; caller_obligation := no_caller_obligation
   ; callee_obligation := no_callee_obligation
   |}.

(** A similar —and as simple— contract is the one that forbids the use of a
    given interface. *)

Definition do_no_use {i Ω} (ω : Ω) (α : Type) (e : i α) : Prop := False.

Definition forbid_specs (i : interface) : contract_m i M unit :=
  {| witness_update := const_witness
   ; caller_obligation := do_no_use
   ; callee_obligation := no_callee_obligation
   |}.

End s_contract.

(* ========================================================================= *)

Definition contract_m_caller_equ
    `(c1 : contract_m i M Ω1)
    `(c2 : contract_m i M Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 α (p : i α),
    caller_obligation c1 ω1 p <->
    caller_obligation c2 (f ω1) p.

Definition contract_m_callee_equ
    `(c1 : contract_m i M Ω1)
    `(c2 : contract_m i M Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 α (p : i α) (mx : M α),
    callee_obligation c1 ω1 p mx <->
    callee_obligation c2 (f ω1) p mx.

Definition contract_m_witness_equ
    `(c1 : contract_m i M Ω1)
    `(c2 : contract_m i M Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 α (p : i α) (mx : M α),
    f (witness_update c1 ω1 p mx)
      =
    witness_update c2 (f ω1) p mx.


Inductive contract_m_equ `(c1 : contract_m i M Ω1) `(c2 : contract_m i M Ω2)
  : Type :=
| mk_contract_m_equ (f : Ω1 -> Ω2) (g : Ω2 -> Ω1)
    (iso1 : forall x, f (g x) = x) (iso2 : forall x, g (f x) = x)
    (caller_equ : contract_m_caller_equ c1 c2 f)
    (callee_equ : contract_m_callee_equ c1 c2 f)
    (witness_equ : contract_m_witness_equ c1 c2 f)
  : contract_m_equ c1 c2.

Definition contract_m_iso_lr `(c1 : contract_m i M Ω1) `(c2 : contract_m i M Ω2)
    (equ : contract_m_equ c1 c2) (ω1 : Ω1)
  : Ω2 :=
  match equ with
  | @mk_contract_m_equ _ _ _ _ _ _ f _ _ _ _ _ _ => f ω1
  end.

Definition contract_m_iso_rl `(c1 : contract_m i M Ω1) `(c2 : contract_m i M Ω2)
    (equ : contract_m_equ c1 c2) (ω2 : Ω2)
  : Ω1 :=
  match equ with
  | @mk_contract_m_equ _ _ _ _ _ _ _ g _ _ _ _ _ => g ω2
  end.

Arguments contract_m_iso_lr {i M Ω1 c1 Ω2 c2} (equ ω1).
Arguments contract_m_iso_rl {i M Ω1 c1 Ω2 c2} (equ ω2).

Lemma contract_m_equ_refl `(c : contract_m i M Ω)
  : contract_m_equ c c.

Proof.
  apply mk_contract_m_equ with (f:=fun x => x) (g:=fun x => x); auto.
  + now intros ω α p.
  + now intros ω α p x.
  + now intros ω α p x.
Defined.

Lemma contract_m_equ_sym `(c1 : contract_m i M Ω1) `(c2 : contract_m i M Ω2)
   (equ : contract_m_equ c1 c2)
  : contract_m_equ c2 c1.

Proof.
  induction equ.
  apply mk_contract_m_equ with (f:=g) (g:=f).
  + apply iso2.
  + apply iso1.
  + intros ω α p.
    transitivity (caller_obligation c2 (f (g ω)) p).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros ω α p x.
    transitivity (callee_obligation c2 (f (g ω)) p x).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros ω α p x.
    rewrite <- (iso2 (witness_update c1 (g ω) p x)).
    assert (equ : witness_update c2 ω p x = f (witness_update c1 (g ω) p x)). {
      transitivity (witness_update c2 (f (g ω)) p x).
      + now rewrite iso1.
      + now rewrite witness_equ.
    }
    now rewrite equ.
Defined.

Lemma contract_m_equ_trans `(c1 : contract_m i M Ω1) `(c2 : contract_m i M Ω2)
   `(c3 : contract_m i M Ω3)
   `(is_equ12 : contract_m_equ c1 c2)
   `(is_equ23 : contract_m_equ c2 c3)
  : contract_m_equ c1 c3.

Proof.
  destruct is_equ12 as [f12 g21 isofg12 isogf12 caller_equ12 callee_equ12 witness_equ12].
  destruct is_equ23 as [f23 g32 isofg23 isogf23 caller_equ23 callee_equ23 witness_equ23].
  apply mk_contract_m_equ
    with (f:=fun x => f23 (f12 x)) (g:=fun x => g21 (g32 x)).
  + setoid_rewrite isofg12.
    now setoid_rewrite isofg23.
  + setoid_rewrite isogf23.
    now setoid_rewrite isogf12.
  + intros ω1 α p.
    transitivity (caller_obligation c2 (f12 ω1) p);
      [ now apply caller_equ12
      | now apply caller_equ23 ].
  + intros ω1 α p x.
    transitivity (callee_obligation c2 (f12 ω1) p x); [ now apply callee_equ12
                                                      | now apply callee_equ23 ].
  + intros ω1 α p x.
    rewrite <- witness_equ23.
    assert (equ : f12 (witness_update c1 ω1 p x) = witness_update c2 (f12 ω1) p x)
      by now rewrite <- witness_equ12.
    now rewrite equ.
Defined.

(* ========================================================================= *)

Definition gen_witness_update
    `{MayProvide ix i}
    {Ω α}
    {M : monad}
    (c : contract_m i M Ω)
    (ω : Ω)
    (e : ix α)
    (mx : M α)
  : Ω :=
  match proj_p e with
  | Some e => witness_update c ω e mx
  | None   => ω
  end.

Definition gen_caller_obligation `{MayProvide ix i} {Ω α} {M : monad} (c : contract_m i M Ω)
    (ω :  Ω) (e : ix α)
  : Prop :=
  match proj_p e with
  | Some e => caller_obligation c ω e
  | None => True
  end.

Definition gen_callee_obligation
    `{MayProvide ix i}
    {Ω α}
    {M : monad}
    (c : contract_m i M Ω)
    (ω : Ω)
    (e : ix α)
    (mx : M α)
  : Prop :=
  match proj_p e with
  | Some e => callee_obligation c ω e mx
  | None   => True
  end.

(* ========================================================================= *)

  Definition contract_mprod
    `{Provide ix i, Provide ix j}
    {M : monad}
    {Ωi Ωj}
    (ci : contract_m i M Ωi)
    (cj : contract_m j M Ωj)
  : contract_m ix M (Ωi * Ωj):=
  {| witness_update := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : M α) =>
                         (gen_witness_update ci (fst ω) e x, gen_witness_update cj (snd ω) e x)
  ;  caller_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) =>
                       gen_caller_obligation ci (fst ω) e /\ gen_caller_obligation cj (snd ω) e
  ;  callee_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : M α) =>
                   gen_callee_obligation ci (fst ω) e x /\ gen_callee_obligation cj (snd ω) e x
  |}.

Infix "*" := contract_mprod : contract_scope.

Definition sharedcontractprod `{Provide ix i, Provide ix j} {M: monad}
   `(ci : contract_m i M Ω) (cj : contract_m j M Ω)
  : contract_m ix M Ω :=
  {|
  witness_update :=
    fun (ω : Ω) (α : Type) (e : ix α) (x : M α) =>
      (* we need to check [i] before [j] because [sharedcontractprod]
         will be right associative *)
      match proj_p (i:=i) e with
      | Some e => witness_update ci ω e x
      | _ => match proj_p (i:=j) e with
             | Some e => witness_update cj ω e x
             | _ => ω
             end
      end;
  caller_obligation :=
    fun (ω : Ω) (α : Type) (e : ix α) =>
      gen_caller_obligation ci ω e /\ gen_caller_obligation cj ω e;
  callee_obligation :=
    fun (ω : Ω) (α : Type) (e : ix α) (x : M α) =>
      gen_callee_obligation ci ω e x /\ gen_callee_obligation cj ω e x
  |}.

Infix "^" := sharedcontractprod  : contract_scope.

(* ========================================================================= *)

Section s_store.
  Context (S : UU0) {M : stateMonad S}.
Check witness_update.
(*      : forall (i : interface) (M : monad) (Ω : UU0), contract_m i M Ω -> Ω -> forall α : UU0, i α -> M α -> Ω *)
Definition store_update : S -> forall α : UU0, STORE S α -> M α -> M α.
move => x A e m.
inversion e; subst. 
- apply/get.
- apply/put/x0.
Defined.

Inductive o_callee_store (x : S) : forall (α : Type), STORE S α -> M α -> Prop :=
| get_o_callee (x' : M S) (equ : Ret x = x') : o_callee_store x S Get x'
| put_o_callee (x' : S) (u : M unit) : o_callee_store x unit (Put x') u.

Definition store_specs : contract_m (STORE S) M S :=
  {| witness_update := store_update
  ;  caller_obligation := no_caller_obligation
  ;  callee_obligation := o_callee_store
  |}.

Definition store_update (s : Type) {M : stateMonad s} . :=
  fun (x : s) (α : Type) (e : STORE s α) (_ : M α) =>
    match e with
    | Get => get
    | Put x' => put x'
    end.

  Check store_update.
  Check stateMonad.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equivalent to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Inductive o_callee_store (s : Type) (x : s) : forall (α : Type), STORE s α -> α -> Prop :=
| get_o_callee (x' : s) (equ : x = x') : o_callee_store s x s Get x'
| put_o_callee (x' : s) (u : unit) : o_callee_store s x unit (Put x') u.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (s : Type) : contract (STORE s) s :=
  {| witness_update := store_update s
  ;  caller_obligation := no_caller_obligation
  ;  callee_obligation := o_callee_store s
  |}.

(** Now, as we briefly mentionned, this contract allows for reasoning about an
    impure computation which uses the [STORE s] interface, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [callee_obligation] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    interfaces, we can actually define several contracts to consider
    different set of hypotheses. *)
