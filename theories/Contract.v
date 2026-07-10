(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on effects, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From FreerDPS Require Import Init.
From FreerDPS Require Import Effect Freer.
#[local]
Open Scope signature_scope.
Open Scope monae_scope.

Generalizable All Variables.

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
    contracts also define a dedicated function [witness_update]. *)

Record contract (F : effect) (St : Type) : Type := make_contract
  { witness_update (*state_upd*) : St -> forall (α : Type), F α -> α -> St
  ; caller_obligation(*precond*) : St -> forall (α : Type), F α -> Prop
  ; callee_obligation(*postcond*) : St -> forall (α : Type), F α -> α -> Prop
  }.

Declare Scope contract_scope.
Bind Scope contract_scope with contract.

Arguments make_contract [F St] (_ _ _).
Arguments witness_update [F St] (c s) [α] (_ _).
Arguments caller_obligation [F St] (c s) [α] (_).
Arguments callee_obligation [F St] (c s) [α] (_ _).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given effect, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {F} :=
  fun (u : unit) (α : Type) (op : F α) (x : α) => u.

Inductive no_caller_obligation {F St} (s : St) (α : Type) (op : F α) : Prop :=
| mk_no_caller_obligation : no_caller_obligation s α op.

#[global] Hint Constructors no_caller_obligation : freespec.

Inductive no_callee_obligation {F St} (s : St) (α : Type)
    (op : F α) (x : α) : Prop :=
| mk_no_callee_obligation : no_callee_obligation s α op x.

#[global] Hint Constructors no_callee_obligation : freespec.

Definition no_contract (F : effect) : contract F unit :=
  {| witness_update := const_witness
   ; caller_obligation := no_caller_obligation
   ; callee_obligation := no_callee_obligation
   |}.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)

Definition do_no_use {F St} (s : St) (α : Type) (op : F α) : Prop := False.

Definition forbid_specs (F : effect) : contract F unit :=
  {| witness_update := const_witness
   ; caller_obligation := do_no_use
   ; callee_obligation := no_callee_obligation
   |}.

(** * Contract Equivalence *)

Definition contract_caller_equ `(c1 : contract F S1) `(c2 : contract F S2)
    (f : S1 -> S2)
  : Prop :=
  forall s1 a (p : F a),
    caller_obligation c1 s1 p <-> caller_obligation c2 (f s1) p.

Definition contract_callee_equ `(c1 : contract F S1) `(c2 : contract F S2)
    (f : S1 -> S2)
  : Prop :=
  forall s1 a (p : F a) x,
    callee_obligation c1 s1 p x <-> callee_obligation c2 (f s1) p x.

Definition contract_witness_equ `(c1 : contract F S1) `(c2 : contract F S2)
    (f : S1 -> S2)
  : Prop :=
  forall s1 a (p : F a) x,
    f (witness_update c1 s1 p x) = witness_update c2 (f s1) p x.

Inductive contract_equ `(c1 : contract F S1) `(c2 : contract F S2)
  : Type :=
| mk_contract_equ (f : S1 -> S2) (g : S2 -> S1)
    (iso1 : forall x, f (g x) = x) (iso2 : forall x, g (f x) = x)
    (caller_equ : contract_caller_equ c1 c2 f)
    (callee_equ : contract_callee_equ c1 c2 f)
    (witness_equ : contract_witness_equ c1 c2 f)
  : contract_equ c1 c2.

Definition contract_iso_lr `(c1 : contract F S1) `(c2 : contract F S2)
    (equ : contract_equ c1 c2) (s1 : S1)
  : S2 :=
  match equ with
  | @mk_contract_equ _ _ _ _ _ f _ _ _ _ _ _ => f s1
  end.

Definition contract_iso_rl `(c1 : contract F S1) `(c2 : contract F S2)
    (equ : contract_equ c1 c2) (s2 : S2)
  : S1 :=
  match equ with
  | @mk_contract_equ _ _ _ _ _ _ g _ _ _ _ _ => g s2
  end.

Arguments contract_iso_lr {F S1 c1 S2 c2} (equ s1).
Arguments contract_iso_rl {F S1 c1 S2 c2} (equ s2).

Lemma contract_equ_refl `(c : contract F St)
  : contract_equ c c.

Proof.
  apply mk_contract_equ with (f:=fun x => x) (g:=fun x => x); auto.
  + now intros s α p.
  + now intros s α p x.
  + now intros s α p x.
Defined.

Lemma contract_equ_sym `(c1 : contract F S1) `(c2 : contract F S2)
   (equ : contract_equ c1 c2)
  : contract_equ c2 c1.

Proof.
  induction equ.
  apply mk_contract_equ with (f:=g) (g:=f).
  + apply iso2.
  + apply iso1.
  + intros s α p.
    transitivity (caller_obligation c2 (f (g s)) p).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros s α p x.
    transitivity (callee_obligation c2 (f (g s)) p x).
    ++ now rewrite iso1.
    ++ now symmetry.
  + intros s α p x.
    rewrite <- (iso2 (witness_update c1 (g s) p x)).
    assert (equ : witness_update c2 s p x = f (witness_update c1 (g s) p x)). {
      transitivity (witness_update c2 (f (g s)) p x).
      + now rewrite iso1.
      + now rewrite witness_equ.
    }
    now rewrite equ.
Defined.

Lemma contract_equ_trans `(c1 : contract F S1) `(c2 : contract F S2)
   `(c3 : contract F S3)
   `(is_equ12 : contract_equ c1 c2)
   `(is_equ23 : contract_equ c2 c3)
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
  + intros s1 α p.
    transitivity (caller_obligation c2 (f12 s1) p);
      [ now apply caller_equ12
      | now apply caller_equ23 ].
  + intros s1 α p x.
    transitivity (callee_obligation c2 (f12 s1) p x); [ now apply callee_equ12
                                                      | now apply callee_equ23 ].
  + intros s1 α p x.
    rewrite <- witness_equ23.
    assert (equ : f12 (witness_update c1 s1 p x) = witness_update c2 (f12 s1) p x)
      by now rewrite <- witness_equ12.
    now rewrite equ.
Defined.

(** * Composing Contracts *)

(** As we compose effects and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F]
    and [E], two effects, if we can reason about [F] and [E] independently
    (e.g., the caller obligations of [E] do not vary when we use [F]), then we
    can compose [cF : contract F SF] and [cE : contract E SE], such that
    [contractprod cF cE] is a contract for [F + E]. *)

Definition gen_witness_update {Fx : effect} `{MayProvide Fx F} {St α}
    (c : contract F St)
    (s :  St) (op : Fx α) (x : α)
  : St :=
  match proj_p op with
  | Some op => witness_update c s op x
  | None => s
  end.

Definition gen_caller_obligation {Fx : effect} `{MayProvide Fx F} {St α}
    (c : contract F St)
    (s :  St) (op : Fx α)
  : Prop :=
  match proj_p op with
  | Some op => caller_obligation c s op
  | None => True
  end.

Definition gen_callee_obligation {Fx : effect} `{MayProvide Fx F} {St α}
    (c : contract F St)
    (s :  St) (op : Fx α) (x : α)
  : Prop :=
  match proj_p op with
  | Some op => callee_obligation c s op x
  | None => True
  end.

Definition contractprod {Fx : effect} `{Provide Fx F, Provide Fx E} {SF SE}
    (cF : contract F SF) (cE : contract E SE)
  : contract Fx (SF * SE) :=
  {| witness_update :=
       fun (s : SF * SE) (α : Type) (op : Fx α) (x : α) =>
         (gen_witness_update cF (fst s) op x,
          gen_witness_update cE (snd s) op x)
  ; caller_obligation :=
      fun (s : SF * SE) (α : Type) (op : Fx α) =>
        gen_caller_obligation cF (fst s) op /\
        gen_caller_obligation cE (snd s) op
  ; callee_obligation :=
      fun (s : SF * SE) (α : Type) (op : Fx α) (x : α) =>
        gen_callee_obligation cF (fst s) op x /\
        gen_callee_obligation cE (snd s) op x
  |}.

Infix "*" := contractprod : contract_scope.

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)

(* FIXME: Should be [StrictProvide2 Fx F E] *)

Definition sharedcontractprod {Fx : effect} `{Provide Fx F, Provide Fx E}
   `(cF : contract F St) (cE : contract E St)
  : contract Fx St :=
  {|
  witness_update :=
    fun (s : St) (α : Type) (op : Fx α) (x : α) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match proj_p (F:=F) op with
      | Some op => witness_update cF s op x
      | _ => match proj_p (F:=E) op with
             | Some op => witness_update cE s op x
             | _ => s
             end
      end;
  caller_obligation :=
    fun (s : St) (α : Type) (op : Fx α) =>
      gen_caller_obligation cF s op /\ gen_caller_obligation cE s op;
  callee_obligation :=
    fun (s : St) (α : Type) (op : Fx α) (x : α) =>
      gen_callee_obligation cF s op x /\ gen_callee_obligation cE s op x
  |}.

Infix "^" := sharedcontractprod  : contract_scope.

(** * Contract By Example *)

(** Finally, and as an example, we define a contract for the effect
    [STORE s] we discuss in [FreerDPS.Freer].  As a reminder, the
    effect is defined as follows:

<<
Inductive STORE (s : Type) : effect :=
| Get : STORE s s
| Put (x : s) : STORE s unit.
>>

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (s : Type) :=
  fun (x : s) (α : Type) (op : STORE s α) (_ : α) =>
    match op with
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
    impure computation which uses the [STORE s] effect, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [callee_obligation] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    effects, we can actually define several contracts to consider
    different set of hypotheses. *)
