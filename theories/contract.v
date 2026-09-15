(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on effs, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From mathcomp Require Import ssreflect.
From FreerDPS Require Import effect freer mathcomp_extra.
From HB Require Import structures.
#[local]
Open Scope signature_scope.
Open Scope monae_scope.

(** * Definition *)

(** A contract dedicated to [F : effect] primarily provides two
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
    state of the effect implementor.

    To keep this state up-to-date after each primitive interpretation,
    contracts also define a dedicated function [state_update]. *)

Section contract_def.
Context (F : effect) (T : Type).

Record contract : Type := make_contract {
  state_update : T -> forall U : Type, F U -> U -> T ;
  requirement : T -> forall U : Type, F U -> Prop ;
  promise : T -> forall U : Type, F U -> U -> Prop }.

End contract_def.



Declare Scope contract_scope.
Bind Scope contract_scope with contract.

Arguments make_contract [F T] (_ _ _).
Arguments state_update [F T] (c _) [U] (_ _).
Arguments requirement [F T] (c _) [U] (_).
Arguments promise [F T] (c _) [U] (_ _).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given effect, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {F : effect} :=
  fun (u : unit) (α : Type) (e : F α) (x : α) => u.

Definition no_requirement {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) : Prop :=
  True.

Definition no_promise {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) (x : α) : Prop :=
  True.

Definition no_contract (F : effect) : contract F unit :=
  make_contract const_witness no_requirement no_promise.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)

Definition do_no_use {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) : Prop :=
  False.

Definition forbid_specs (F : effect) : contract F unit :=
  {| state_update := const_witness
   ; requirement := do_no_use
   ; promise := no_promise
   |}.

(** * Contract Equivalence *)

Definition contract_caller_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a),
    requirement c1 ω1 p <-> requirement c2 (f ω1) p.

Definition contract_callee_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a) x,
    promise c1 ω1 p x <-> promise c2 (f ω1) p x.

Definition contract_witness_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a) x,
    f (state_update c1 ω1 p x) = state_update c2 (f ω1) p x.

Inductive contract_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2) : Type :=
| mk_contract_equ (f : Ω1 -> Ω2) (g : Ω2 -> Ω1)
    (iso1 : forall x, f (g x) = x) (iso2 : forall x, g (f x) = x)
    (caller_equ : contract_caller_equ c1 c2 f)
    (callee_equ : contract_callee_equ c1 c2 f)
    (witness_equ : contract_witness_equ c1 c2 f)
  : contract_equ c1 c2.

Definition contract_iso_lr {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (equ : contract_equ c1 c2) (ω1 : Ω1)
  : Ω2 :=
  match equ with
  | @mk_contract_equ _ _ _ _ _ f _ _ _ _ _ _ => f ω1
  end.

Definition contract_iso_rl {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (equ : contract_equ c1 c2) (ω2 : Ω2)
  : Ω1 :=
  match equ with
  | @mk_contract_equ _ _ _ _ _ _ g _ _ _ _ _ => g ω2
  end.

Arguments contract_iso_lr {F Ω1 Ω2 c1 c2} (equ ω1).
Arguments contract_iso_rl {F Ω1 Ω2 c1 c2} (equ ω2).

Lemma contract_equ_refl {F : effect} {Ω : Type} (c : contract F Ω)
  : contract_equ c c.

Proof.
  apply mk_contract_equ with (f:=fun x => x) (g:=fun x => x); auto.
  + now intros ω α p.
  + now intros ω α p x.
  + now intros ω α p x.
Defined.

Lemma contract_equ_sym {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
   (equ : contract_equ c1 c2)
  : contract_equ c2 c1.

Proof.
  induction equ.
  apply mk_contract_equ with (f:=g) (g:=f).
  + apply iso2.
  + apply iso1.
  + intros ω α p.
    transitivity (requirement c2 (f (g ω)) p).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros ω α p x.
    transitivity (promise c2 (f (g ω)) p x).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros ω α p x.
    rewrite <- (iso2 (state_update c1 (g ω) p x)).
    assert (equ : state_update c2 ω p x = f (state_update c1 (g ω) p x)). {
      transitivity (state_update c2 (f (g ω)) p x).
      + now rewrite iso1.
      + now rewrite witness_equ.
    }
    now rewrite equ.
Defined.

Lemma contract_equ_trans {F : effect} {Ω1 Ω2 Ω3 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (c3 : contract F Ω3)
    (is_equ12 : contract_equ c1 c2)
    (is_equ23 : contract_equ c2 c3)
  : contract_equ c1 c3.

Proof.
  destruct is_equ12 as [f12 g21 isofg12 isogf12 caller_equ12 callee_equ12 witness_equ12].
  destruct is_equ23 as [f23 g32 isofg23 isogf23 caller_equ23 callee_equ23 witness_equ23].
  apply mk_contract_equ
    with (f:=fun x => f23 (f12 x)) (g:=fun x => g21 (g32 x)).
  + setoid_rewrite isofg12.
    now setoid_rewrite isofg23.
  + setoid_rewrite isogf23.
    now setoid_rewrite isogf12.
  + intros ω1 α p.
    transitivity (requirement c2 (f12 ω1) p);
      [ now apply caller_equ12
      | now apply caller_equ23 ].
  + intros ω1 α p x.
    transitivity (promise c2 (f12 ω1) p x); [ now apply callee_equ12
                                                      | now apply callee_equ23 ].
  + intros ω1 α p x.
    rewrite <- witness_equ23.
    assert (equ : f12 (state_update c1 ω1 p x) = state_update c2 (f12 ω1) p x)
      by now rewrite <- witness_equ12.
    now rewrite equ.
Defined.

(** * Composing Contracts *)

(** As we compose effs and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F] and [E]
    two effs, if we can reason about [F] and [E] independently (e.g., the
    caller obligations of [E] do not vary when we use [F]), then we can compose
    [ci : contract F ΩF] and [cj : contract E ΩE], such that [contractprod ci cj] in a
    contract for [F + E]. *)

(* HB.lock  *)
Definition gen_state_update {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α) (x : α)
  : Ω :=
  if prj e is Some e then state_update c ω e x else ω.
Arguments gen_state_update : simpl never.

Definition gen_requirement {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α)
  : Prop :=
  if prj e is Some e then requirement c ω e else True.

Definition gen_promise {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α) (x : α)
  : Prop :=
  if prj e is Some e then promise c ω e x else True.

Definition contractprod {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : Type}
    (ci : contract F ΩF) (cj : contract E ΩE)
  : contract Fx (ΩF * ΩE) :=
  {| state_update := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) (x : α) =>
                         (gen_state_update ci (fst ω) e x, gen_state_update cj (snd ω) e x)
  ;  requirement := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) =>
                       gen_requirement ci (fst ω) e /\ gen_requirement cj (snd ω) e
  ;  promise := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) (x : α) =>
                   gen_promise ci (fst ω) e x /\ gen_promise cj (snd ω) e x
  |}.

Infix "-*-" := contractprod (at level 20) : contract_scope .

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)
Section s.
Context {Fx : effect}.
Definition sharedcontractprod {F E : effect} `{F ;; E -<< Fx}
    {Ω : Type} (ci : contract F Ω) (cj : contract E Ω)
  : contract Fx Ω :=
  {|
  state_update :=
    fun (ω : Ω) (α : Type) (e : Fx α) (x : α) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match prj (F:=F) e with
      | Some e => state_update ci ω e x
      | _ => if prj (F:=E) e is Some e then state_update cj ω e x else ω
      end;
  requirement :=
    fun (ω : Ω) (α : Type) (e : Fx α) =>
      gen_requirement ci ω e /\ gen_requirement cj ω e;
  promise :=
    fun (ω : Ω) (α : Type) (e : Fx α) (x : α) =>
      gen_promise ci ω e x /\ gen_promise cj ω e x
  |}.

End s.
Infix "-^-" := sharedcontractprod (at level 20, right associativity) : contract_scope.
(** * Contract By Example *)

(** Finally, and as an example, we define a contract for the effect
    [STORE s] we discuss in [FreerDPS.Freer].

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (s : Type) :=
  fun (x : s) (α : Type) (e : STORE s α) (_ : α) =>
    match e with
    | Get => x
    | Put x' => x'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equivalent to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Definition o_callee_store (s : Type) (x : s) :
    forall α, STORE s α -> α -> Prop :=
  fun α op =>
    match op in STORE _ α return α -> Prop with
    | Get => fun x' => x = x'
    | Put _ => fun _ => True
    end.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (s : Type) : contract (STORE s) s :=
  {| state_update := store_update s
  ;  requirement := no_requirement
  ;  promise := o_callee_store s
  |}.

(** Now, as we briefly mentionned, this contract allows for reasoning about an
    impure computation which uses the [STORE s] effect, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [promise] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    effs, we can actually define several contracts to consider
    different set of hypotheses. *)


Section contract_helpers.
Context {Fx F : effect} `{F -< Fx} {W X Y : Type}
    (c : contract F W) (w w' : W) (op : F X) (op' : F Y)
    (x : X) (concl : Prop).

Local Notation inj := (inj (Fx:=Fx)).

Lemma provided_callerP :
  gen_requirement c w (inj op)
  <-> requirement c w op.
Proof.
by rewrite /gen_requirement !injK_Some.
Qed.

Lemma provided_bind_caller :
  (promise c w op x ->
    requirement c (state_update c w op x) op') ->
  gen_promise c w (inj op) x ->
  gen_requirement c
    (gen_state_update c w (inj op) x)
    (inj op').
Proof.
rewrite /gen_state_update /gen_promise.
by rewrite /gen_requirement !injK_Some.
Qed.


Lemma provided_calleeP :
  (w' = gen_state_update c w (inj op) x
  /\ gen_promise c w (inj op) x )
  <-> (w' = state_update c w op x /\ promise c w op x) .
Proof.
by split; rewrite /gen_promise /gen_state_update !injK_Some.
Qed.

End contract_helpers.

Section contract_distinguish_helpers.
Context {Fx F G : effect} `{F -<? Fx} `{G -< Fx}
    `{Distinguish Fx G F}
    {W X : Type} (c : contract F W) (w w' : W) (op : G X) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma distinguished_caller :
  gen_requirement c w (inj op).
Proof.
by rewrite /gen_requirement injK_None.
Qed.

Lemma distinguished_callee :
  (w' = gen_state_update c w (inj op) x /\
    gen_promise c w (inj op) x) <->
  w' = w.
Proof.
rewrite /gen_state_update /gen_promise injK_None.
by split=> [[-> _] | ->].
Qed.
End contract_distinguish_helpers.


Section shared_contract_helpers.
Context {Fx F G : effect}.
Context `{S: F;; G -<< Fx}
    {W X : Type} (ci : contract F W) (cj : contract G W)
    (w w' : W) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma shared_left_callerP (op : F X) :
  gen_requirement
    (ci -^- cj) w (inj op)
  <-> requirement ci w op.
Proof.
split.
- Set Printing Implicit. by case=> + _; rewrite provided_callerP.
- move=> caller; split.
  + rewrite provided_callerP; exact: caller.
  + by rewrite /gen_requirement (@injK_None Fx F G).
Qed.

Lemma shared_right_callerP (op : G X) :
  gen_requirement (Fx := Fx)
    (ci -^- cj) w (inj op)
  <-> requirement cj w op.
Proof.
split.
- by case=> _; rewrite provided_callerP.
- move=> caller; split.
  + by rewrite /gen_requirement (@injK_None Fx G F).
  + rewrite provided_callerP; exact: caller.
Qed.

Lemma shared_left_calleeP (op : F X) :
  (w' = gen_state_update (Fx := Fx)
      (ci -^- cj) w
      (inj op) x /\
    gen_promise (Fx := Fx)
      (ci -^- cj) w
      (inj op) x) <->
  w' = state_update ci w op x /\ promise ci w op x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite (@injK_Some Fx F) (@injK_None Fx F G).
by tauto.
Qed.

Lemma shared_right_calleeP (op : G X) :
  (w' = gen_state_update (Fx := Fx)
      (ci -^- cj) w
      (inj op) x /\
    gen_promise (Fx := Fx)
      (ci -^- cj) w
      (inj op) x) <->
  w' = state_update cj w op x /\ promise cj w op x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite (@injK_None Fx G F) (@injK_Some Fx G).
by tauto.
Qed.
End shared_contract_helpers.

Section shared_contract_inj_helpers.
Context {H Fx F G : effect} `{F;; G-<<Fx, Fx -< H}
    {W X : Type} (ci : contract F W) (cj : contract G W)
    (w w' : W) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma shared_left_caller_injP (op : F X) :
  gen_requirement
    (sharedcontractprod (Fx:=Fx) ci cj) w (effect.injT H Fx F _ op)
  <-> requirement ci w op.
Proof.
split; rewrite provided_callerP /= provided_callerP.
- by case=> + _.
- move=> caller; split.
  + exact: caller.
  + by rewrite /gen_requirement (@injK_None Fx F G).
Qed.

Lemma shared_right_caller_injP (op : G X) :
  gen_requirement
    (ci -^- cj) w (effect.injT H Fx G _ op)
  <-> requirement cj w op.
Proof.
split; rewrite provided_callerP /= provided_callerP.
- by case=> _.
- move=> caller; split.
  + by rewrite /gen_requirement (@injK_None Fx G F).
  + exact: caller.
Qed.

Lemma shared_left_callee_injP (op : F X) :
  (w' = gen_state_update
      (ci -^- cj) w
      (effect.injT H Fx F _ op) x /\
    gen_promise
      (ci -^- cj) w
      (effect.injT H Fx F _ op) x) <->
  w' = state_update ci w op x /\ promise ci w op x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite !injK_Some injK_None.
by tauto.
Qed.

Lemma shared_right_callee_injP (op : G X) :
  (w' = gen_state_update
      (ci -^- cj) w
      (effect.injT H Fx G _ op) x /\
    gen_promise
      (ci -^- cj) w
      (effect.injT H Fx G _ op) x) <->
  w' = state_update cj w op x /\ promise cj w op x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite !injK_Some injK_None.
by tauto.
Qed.
End shared_contract_inj_helpers.
