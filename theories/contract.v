(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on effs, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From mathcomp Require Import ssreflect seq.
From FreerDPS Require Import effect freer.
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
    contracts also define a dedicated function [witness_update]. *)

Record contract (F : effect) (Ω : Type) : Type := make_contract
  { witness_update (ω : Ω) : forall (α : Type), F α -> α -> Ω
  ; caller_obligation (ω : Ω) : forall (α : Type),  F α -> Prop
  ; callee_obligation (ω : Ω) : forall (α : Type), F α -> α -> Prop
  }.

Declare Scope contract_scope.
Bind Scope contract_scope with contract.

Arguments make_contract [F Ω] (_ _ _).
Arguments witness_update [F Ω] (c ω) [α] (_ _).
Arguments caller_obligation [F Ω] (c ω) [α] (_).
Arguments callee_obligation [F Ω] (c ω) [α] (_ _).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given effect, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {F : effect} :=
  fun (u : unit) (α : Type) (e : F α) (x : α) => u.

Definition no_caller_obligation {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) : Prop :=
  True.

Definition no_callee_obligation {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) (x : α) : Prop :=
  True.

Definition no_contract (F : effect) : contract F unit :=
  {| witness_update := const_witness
   ; caller_obligation := no_caller_obligation
   ; callee_obligation := no_callee_obligation
   |}.

(** A similar —and as simple— contract is the one that forbids the use of a
    given effect. *)

Definition do_no_use {F : effect} {Ω : Type}
    (ω : Ω) (α : Type) (e : F α) : Prop :=
  False.

Definition forbid_specs (F : effect) : contract F unit :=
  {| witness_update := const_witness
   ; caller_obligation := do_no_use
   ; callee_obligation := no_callee_obligation
   |}.

(** * Contract Equivalence *)

Definition contract_caller_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a),
    caller_obligation c1 ω1 p <-> caller_obligation c2 (f ω1) p.

Definition contract_callee_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a) x,
    callee_obligation c1 ω1 p x <-> callee_obligation c2 (f ω1) p x.

Definition contract_witness_equ {F : effect} {Ω1 Ω2 : Type}
    (c1 : contract F Ω1) (c2 : contract F Ω2)
    (f : Ω1 -> Ω2)
  : Prop :=
  forall ω1 a (p : F a) x,
    f (witness_update c1 ω1 p x) = witness_update c2 (f ω1) p x.

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

(** * Composing Contracts *)

(** As we compose effs and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [F] and [E]
    two effs, if we can reason about [F] and [E] independently (e.g., the
    caller obligations of [E] do not vary when we use [F]), then we can compose
    [ci : contract F ΩF] and [cj : contract E ΩE], such that [contractprod ci cj] in a
    contract for [F + E]. *)

(* HB.lock  *)
Definition gen_witness_update {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α) (x : α)
  : Ω :=
  if prj e is Some e then witness_update c ω e x else ω.
(* Canonical locked_gen_witness_update := Unlockable gen_witness_update.unlock. *)
Arguments gen_witness_update : simpl never.

Definition gen_caller_obligation {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α)
  : Prop :=
  if prj e is Some e then caller_obligation c ω e else True.

Definition gen_callee_obligation {Fx F : effect} `{F -<? Fx}
    {Ω α : Type} (c : contract F Ω)
    (ω :  Ω) (e : Fx α) (x : α)
  : Prop :=
  if prj e is Some e then callee_obligation c ω e x else True.

Definition contractprod {Fx F E : effect} `{F -< Fx, E -< Fx}
    {ΩF ΩE : Type}
    (ci : contract F ΩF) (cj : contract E ΩE)
  : contract Fx (ΩF * ΩE) :=
  {| witness_update := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) (x : α) =>
                         (gen_witness_update ci (fst ω) e x, gen_witness_update cj (snd ω) e x)
  ;  caller_obligation := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) =>
                       gen_caller_obligation ci (fst ω) e /\ gen_caller_obligation cj (snd ω) e
  ;  callee_obligation := fun (ω : ΩF * ΩE) (α : Type) (e : Fx α) (x : α) =>
                   gen_callee_obligation ci (fst ω) e x /\ gen_callee_obligation cj (snd ω) e x
  |}.

Infix "-*-" := contractprod (at level 20) : contract_scope .

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)

Definition sharedcontractprod {Fx F E : effect}
    `{[:: F; E] -<< Fx}
    {Ω : Type} (ci : contract F Ω) (cj : contract E Ω)
  : contract Fx Ω :=
  {|
  witness_update :=
    fun (ω : Ω) (α : Type) (e : Fx α) (x : α) =>
      (* we need to check [F] before [E] because [sharedcontractprod]
         will be right associative *)
      match prj (F:=F) e with
      | Some e => witness_update ci ω e x
      | _ => if prj (F:=E) e is Some e then witness_update cj ω e x else ω
      end;
  caller_obligation :=
    fun (ω : Ω) (α : Type) (e : Fx α) =>
      gen_caller_obligation ci ω e /\ gen_caller_obligation cj ω e;
  callee_obligation :=
    fun (ω : Ω) (α : Type) (e : Fx α) (x : α) =>
      gen_callee_obligation ci ω e x /\ gen_callee_obligation cj ω e x
  |}.

Infix "-^-" := sharedcontractprod (at level 20, right associativity) : contract_scope.

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
    effs, we can actually define several contracts to consider
    different set of hypotheses. *)


Section contract_helpers.
Context {Fx F : effect} {Hfxf : F -< Fx} {W X Y : Type}
    (c : contract F W) (w w' : W) (op : F X) (op' : F Y)
    (x : X) (concl : Prop).

Lemma provided_callerP :
  gen_caller_obligation (H := Hfxf.(may_prov)) c w (inj op)
  <-> caller_obligation c w op.
Proof.
by rewrite /gen_caller_obligation !injK_Some.
Qed.

Lemma provided_bind_caller :
  (callee_obligation c w op x ->
    caller_obligation c (witness_update c w op x) op') ->
  gen_callee_obligation (H := Hfxf.(may_prov)) c w (inj op) x ->
  gen_caller_obligation (H := Hfxf.(may_prov)) c
    (gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x)
    (inj op').
Proof.
rewrite /gen_witness_update /gen_callee_obligation.
by rewrite /gen_caller_obligation !injK_Some.
Qed.


Lemma provided_calleeP :
  (w' = gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x /\ gen_callee_obligation (H := Hfxf.(may_prov)) c w (inj op) x )
  <-> (w' = witness_update c w op x /\ callee_obligation c w op x) .
Proof.
by split; rewrite /gen_callee_obligation /gen_witness_update !injK_Some.
Qed.

(* Lemma provided_callee :
  (callee_obligation c w op x ->
    w' = witness_update c w op x) <->
  (gen_callee_obligation (H := Hfxf.(may_prov)) c w (inj op) x ->
  w' = gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x).
Proof.
by split; rewrite /gen_callee_obligation /gen_witness_update !injK_Some.
Qed.

Lemma provided_callee_run :
  (callee_obligation c w op x ->
    w' = witness_update c w op x -> concl) ->
  gen_callee_obligation (H := Hfxf.(may_prov)) c w (inj op) x ->
  w' = gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x ->
  concl.
Proof.
by rewrite /gen_callee_obligation /gen_witness_update !injK_Some.
Qed.

Lemma provided_callee_bind_run :
  (callee_obligation c w op x ->
    (exists y : Y,
      w' = witness_update c (witness_update c w op x) op' y /\
      callee_obligation c (witness_update c w op x) op' y) ->
    concl) ->
  gen_callee_obligation (H := Hfxf.(may_prov)) c w (inj op) x ->
  (exists y : Y,
    w' = gen_witness_update (H := Hfxf.(may_prov)) c
      (gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x)
      (inj op') y /\
    gen_callee_obligation (H := Hfxf.(may_prov)) c
      (gen_witness_update (H := Hfxf.(may_prov)) c w (inj op) x)
      (inj op') y) ->
  concl.
Proof.
by rewrite /gen_callee_obligation /gen_witness_update !injK_Some.
Qed. *)
End contract_helpers.

Section contract_distinguish_helpers.
Context {Fx F G : effect} {Hfxf : F -<? Fx} {Hfxg : G -< Fx}
    {Hdist : @Distinguish Fx G F Hfxg Hfxf}
    {W X : Type} (c : contract F W) (w w' : W) (op : G X) (x : X).

Lemma distinguished_caller :
  gen_caller_obligation (H := Hfxf) c w (inj op).
Proof.
by rewrite /gen_caller_obligation injK_None.
Qed.

Lemma distinguished_callee :
  (w' = gen_witness_update (H := Hfxf) c w (inj op) x /\
    gen_callee_obligation (H := Hfxf) c w (inj op) x) <->
  w' = w.
Proof.
rewrite /gen_witness_update /gen_callee_obligation injK_None.
by split=> [[-> _] | ->].
Qed.
End contract_distinguish_helpers.


Section shared_contract_helpers.
Context {Fx F G : effect} `{[:: F; G] -<< Fx}
    {W X : Type} (ci : contract F W) (cj : contract G W)
    (w w' : W) (x : X).

Lemma shared_left_callerP (op : F X) :
  gen_caller_obligation (Fx := Fx)
    (sharedcontractprod (Fx := Fx) ci cj) w (inj (Fx := Fx) op)
  <-> caller_obligation ci w op.
Proof.
split.
- by case=> + _; rewrite provided_callerP.
- move=> caller; split.
  + rewrite provided_callerP; exact: caller.
  + exact: distinguished_caller.
Qed.

Lemma shared_right_callerP (op : G X) :
  gen_caller_obligation (Fx := Fx)
    (sharedcontractprod (Fx := Fx) ci cj) w (inj (Fx := Fx) op)
  <-> caller_obligation cj w op.
Proof.
split.
- by case=> _; rewrite provided_callerP.
- move=> caller; split.
  + exact: distinguished_caller.
  + rewrite provided_callerP; exact: caller.
Qed.

Lemma shared_left_calleeP (op : F X) :
  (w' = gen_witness_update (Fx := Fx)
      (sharedcontractprod (Fx := Fx) ci cj) w
      (inj (Fx := Fx) op) x /\
    gen_callee_obligation (Fx := Fx)
      (sharedcontractprod (Fx := Fx) ci cj) w
      (inj (Fx := Fx) op) x) <->
  w' = witness_update ci w op x /\ callee_obligation ci w op x.
Proof.
rewrite /gen_witness_update /gen_callee_obligation /=.
rewrite /sharedcontractprod /= /gen_callee_obligation.
rewrite injK_Some injK_None.
by tauto.
Qed.

Lemma shared_right_calleeP (op : G X) :
  (w' = gen_witness_update (Fx := Fx)
      (sharedcontractprod (Fx := Fx) ci cj) w
      (inj (Fx := Fx) op) x /\
    gen_callee_obligation (Fx := Fx)
      (sharedcontractprod (Fx := Fx) ci cj) w
      (inj (Fx := Fx) op) x) <->
  w' = witness_update cj w op x /\ callee_obligation cj w op x.
Proof.
rewrite /gen_witness_update /gen_callee_obligation /=.
rewrite /sharedcontractprod /= /gen_callee_obligation.
rewrite injK_None injK_Some.
by tauto.
Qed.
End shared_contract_helpers.
