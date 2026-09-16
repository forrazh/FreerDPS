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
  fun (u : unit) (T : Type) (e : F T) (x : T) => u.

Definition no_requirement {F : effect} {S : Type}
    (s : S) (T : Type) (e : F T) : Prop :=
  True.

Definition no_promise {F : effect} {S : Type}
    (s : S) (T : Type) (e : F T) (x : T) : Prop :=
  True.

Definition no_contract (F : effect) : contract F unit :=
  make_contract const_witness no_requirement no_promise.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)

Definition do_no_use {F : effect} {S : Type}
    (s : S) (T : Type) (e : F T) : Prop :=
  False.

Definition forbid_specs (F : effect) : contract F unit :=
  {| state_update := const_witness
   ; requirement := do_no_use
   ; promise := no_promise
   |}.

(** * Composing Contracts *)

(** As we compose effs and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F] and [E]
    two effs, if we can reason about [F] and [E] independently (e.g., the
    caller obligations of [E] do not vary when we use [F]), then we can compose
    [ci : contract F ΩF] and [cj : contract E ΩE], such that [contractprod ci cj] in a
    contract for [F + E]. *)

Definition gen_state_update {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s :  S) (e : Fx T) (x : T)
  : S :=
  if prj e is Some e then state_update c s e x else s.
Arguments gen_state_update : simpl never.

Definition gen_requirement {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s :  S) (e : Fx T)
  : Prop :=
  if prj e is Some e then requirement c s e else True.

Definition gen_promise {Fx F : effect} `{F -<? Fx}
    {S T : Type} (c : contract F S)
    (s :  S) (e : Fx T) (x : T)
  : Prop :=
  if prj e is Some e then promise c s e x else True.

Definition contractprod {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : Type}
    (ci : contract F ΩF) (cj : contract E ΩE)
  : contract Fx (ΩF * ΩE) :=
  {| state_update := fun (s : ΩF * ΩE) (T : Type) (e : Fx T) (x : T) =>
                         (gen_state_update ci (fst s) e x, gen_state_update cj (snd s) e x)
  ;  requirement := fun (s : ΩF * ΩE) (T : Type) (e : Fx T) =>
                       gen_requirement ci (fst s) e /\ gen_requirement cj (snd s) e
  ;  promise := fun (s : ΩF * ΩE) (T : Type) (e : Fx T) (x : T) =>
                   gen_promise ci (fst s) e x /\ gen_promise cj (snd s) e x
  |}.

Infix "-*-" := contractprod (at level 20) : contract_scope .

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)
Section s.
Context {Fx : effect}.
Definition sharedcontractprod {F E : effect} `{F ;; E -<< Fx}
    {S : Type} (ci : contract F S) (cj : contract E S)
  : contract Fx S :=
  {|
  state_update :=
    fun (s : S) (T : Type) (e : Fx T) (x : T) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match prj (F:=F) e with
      | Some e => state_update ci s e x
      | _ => if prj (F:=E) e is Some e then state_update cj s e x else s
      end;
  requirement :=
    fun (s : S) (T : Type) (e : Fx T) =>
      gen_requirement ci s e /\ gen_requirement cj s e;
  promise :=
    fun (s : S) (T : Type) (e : Fx T) (x : T) =>
      gen_promise ci s e x /\ gen_promise cj s e x
  |}.

End s.
Infix "-^-" := sharedcontractprod (at level 20, right associativity) : contract_scope.
(** * Contract By Example *)

(** Finally, and as an example, we define a contract for the effect
    [STORE s] we discuss in [FreerDPS.Freer].

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (S : Type) :=
  fun (s : S) (T : Type) (e : STORE S T) (_ : T) =>
    match e with
    | Get => s
    | Put s' => s'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equivalent to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Definition o_callee_store (S : Type) (x : S) :
    forall T, STORE S T -> T -> Prop :=
  fun T cmd =>
    match cmd in STORE _ T return T -> Prop with
    | Get => fun x' => x = x'
    | Put _ => fun _ => True
    end.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (S : Type) : contract (STORE S) S :=
  {| state_update := store_update S
  ;  requirement := no_requirement
  ;  promise := o_callee_store S
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
Context {Fx F : effect} `{F -< Fx} {S X Y : Type}
    (c : contract F S) (s s' : S) (cmd : F X) (cmd' : F Y)
    (x : X) (concl : Prop).

Local Notation inj := (inj (Fx:=Fx)).

Lemma provided_callerP :
  gen_requirement c s (inj cmd)
  <-> requirement c s cmd.
Proof.
by rewrite /gen_requirement !injK_Some.
Qed.

Lemma provided_bind_caller :
  (promise c s cmd x ->
    requirement c (state_update c s cmd x) cmd') ->
  gen_promise c s (inj cmd) x ->
  gen_requirement c
    (gen_state_update c s (inj cmd) x)
    (inj cmd').
Proof.
rewrite /gen_state_update /gen_promise.
by rewrite /gen_requirement !injK_Some.
Qed.


Lemma provided_calleeP :
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x )
  <-> (s' = state_update c s cmd x /\ promise c s cmd x) .
Proof.
by split; rewrite /gen_promise /gen_state_update !injK_Some.
Qed.

End contract_helpers.

Section contract_distinguish_helpers.
Context {Fx F G : effect} `{F -<? Fx} `{G -< Fx}
    `{Distinguish Fx G F}
    {S X : Type} (c : contract F S) (s s' : S) (cmd : G X) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma distinguished_caller :
  gen_requirement c s (inj cmd).
Proof.
by rewrite /gen_requirement injK_None.
Qed.

Lemma distinguished_callee :
  (s' = gen_state_update c s (inj cmd) x /\ gen_promise c s (inj cmd) x)
  <-> s' = s.
Proof.
rewrite /gen_state_update /gen_promise injK_None.
by split=> [[-> _] | ->].
Qed.
End contract_distinguish_helpers.


Section shared_contract_helpers.
Context {Fx F G : effect}.
Context `{F;; G -<< Fx}
    {S X : Type} (ci : contract F S) (cj : contract G S)
    (s s' : S) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma shared_left_callerP (cmd : F X) :
  gen_requirement (ci -^- cj) s (inj cmd)
  <-> requirement ci s cmd.
Proof.
split.
- by case=> + _; rewrite provided_callerP.
- move=> caller; split.
  + rewrite provided_callerP; exact: caller.
  + by rewrite /gen_requirement injK_None.
Qed.

Lemma shared_right_callerP (cmd : G X) :
  gen_requirement (ci -^- cj) s (inj cmd)
  <-> requirement cj s cmd.
Proof.
split.
- by case=> _; rewrite provided_callerP.
- move=> caller; split.
  + by rewrite /gen_requirement injK_None.
  + rewrite provided_callerP; exact: caller.
Qed.

Lemma shared_left_calleeP (cmd : F X) :
  (s' = gen_state_update (ci -^- cj) s (inj cmd) x
    /\ gen_promise (ci -^- cj) s (inj cmd) x)
  <-> s' = state_update ci s cmd x /\ promise ci s cmd x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite injK_Some injK_None.
by tauto.
Qed.

Lemma shared_right_calleeP (cmd : G X) :
  (s' = gen_state_update (ci -^- cj) s (inj cmd) x
    /\ gen_promise (ci -^- cj) s (inj cmd) x)
  <->  s' = state_update cj s cmd x /\ promise cj s cmd x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite injK_None injK_Some.
by tauto.
Qed.
End shared_contract_helpers.

Section shared_contract_inj_helpers.
Context {H Fx F G : effect} `{F;; G-<<Fx, Fx -< H}
    {S X : Type} (ci : contract F S) (cj : contract G S)
    (s s' : S) (x : X).

Local Notation inj := (inj (Fx:=Fx)).

Lemma shared_left_caller_injP (cmd : F X) :
  gen_requirement (ci -^- cj) s (effect.injT H Fx F _ cmd)
    <-> requirement ci s cmd.
Proof.
split; rewrite provided_callerP /= provided_callerP.
- by case=> + _.
- move=> caller; split.
  + exact: caller.
  + by rewrite /gen_requirement injK_None.
Qed.

Lemma shared_right_caller_injP (cmd : G X) :
  gen_requirement (ci -^- cj) s (effect.injT H Fx G _ cmd)
    <-> requirement cj s cmd.
Proof.
split; rewrite provided_callerP /= provided_callerP.
- by case=> _.
- move=> caller; split.
  + by rewrite /gen_requirement injK_None.
  + exact: caller.
Qed.

Lemma shared_left_callee_injP (cmd : F X) :
  (s' = gen_state_update (ci -^- cj) s (effect.injT H Fx F _ cmd) x
    /\ gen_promise (ci -^- cj) s (effect.injT H Fx F _ cmd) x)
  <-> s' = state_update ci s cmd x /\ promise ci s cmd x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite !injK_Some injK_None.
by tauto.
Qed.

Lemma shared_right_callee_injP (cmd : G X) :
  (s' = gen_state_update (ci -^- cj) s (effect.injT H Fx G _ cmd) x
    /\ gen_promise (ci -^- cj) s (effect.injT H Fx G _ cmd) x)
  <-> s' = state_update cj s cmd x /\ promise cj s cmd x.
Proof.
rewrite /gen_state_update /gen_promise /=.
rewrite /sharedcontractprod /= /gen_promise.
rewrite !injK_Some injK_None.
by tauto.
Qed.
End shared_contract_inj_helpers.
