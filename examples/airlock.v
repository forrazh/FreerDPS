(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import all_boot classical_sets boolp.
From monae Require Import hierarchy.
(* WARNING: Move this import to its MathComp counterpart. *)
From Stdlib Require Import Arith.
From FreerDPS Require Import all_freerdps.

(* DOORS == TODO *)

Module Export DoorsControllerM.
(** ** Doors *)

Inductive door : Type := left | right.

HB.instance Definition _ := gen_eqMixin door.

Inductive DOORS : effect :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Section doors_s.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.

Definition is_open (d : door) : M bool := ptrigger $ IsOpen d.
Definition toggle (d : door) : M unit := ptrigger $ Toggle d.
Definition open_door (d : door) : M unit :=
  is_open d >>= fun open => when (~~ open) (toggle d).
Definition close_door (d : door) : M unit :=
  is_open d >>= (when ^~ (toggle d)).
End doors_s.

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| TriggerOpen (d : door) : CONTROLLER unit.

Section controller_s.
Context {Fx : effect} `{CONTROLLER -< Fx} {M : freerMonad Fx}.
Definition tick : M unit := ptrigger Tick.
Definition trigger_open (d : door) : M unit := ptrigger $ TriggerOpen d.
End controller_s.

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller {Fx : effect} `{DOORS -< Fx, STORE nat -< Fx}
    {M : freerMonad Fx} : component (M := M) CONTROLLER Fx :=
  fun _ op =>
    match op with
    | Tick =>
      iget >>= fun cpt =>
      when (15 <? cpt)%nat $
        close_door left >>
        close_door right >>
        iput 0%nat
    | TriggerOpen d =>
      close_door (co d) >>
      open_door d >>
      iput 0%nat
    end.
End DoorsControllerM.

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(* ----------------------------- Witness States ----------------------------- *)

Definition Ω : Type := bool * bool.
(*         S : Type := left * rght. *)

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (~~ (fst ω), snd ω)
  | right => (fst ω, ~~ (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω) :
  sel d (tog d ω) = ~~ sel d ω.
Proof. by case: d. Qed.

Lemma tog_equ_2 (d : door) (ω : Ω) :
  sel (co d) (tog d ω) = sel (co d) ω.
Proof. by case: d. Qed.

Opaque tog.

(* -------------------------------------------------------------------------- *)

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

(* -------------------------------- Contract -------------------------------- *)
(* Ω = bool * bool : doors state *)
Definition step (ω : Ω) (a : Type) (op : DOORS a) (_ : a) : Ω :=
  if op is Toggle d then tog d ω else ω.

(** *** Requirements / Precondition *)
Definition doors_o_caller (ω : Ω) : forall a, DOORS a -> Prop :=
  fun a op =>
    match op with
    (** Given the door [d] of a system [ω], it is always possible to ask for
        the state of [d]. *)
    | IsOpen _ => True
    (** If [d] is closed, the second door [co d] has to be closed too for a
        trigger toggling [d] to be valid. *)
    | Toggle d => sel (co d) ω -> sel d ω
    end.

(** *** Promises / PostCondition *)
Definition doors_o_callee (ω : Ω) : forall a, DOORS a -> a -> Prop :=
  fun a op =>
    match op in DOORS a return a -> Prop with
    (** The reported state of [d] shall reflect its true state. *)
    | IsOpen d => fun opened => sel d ω = opened
    (** A toggle operation has no meaningful result. *)
    | Toggle _ => fun _ => True
    end.

Lemma doors_o_callee_is_openE
    {ω : Ω} {d : door} {opened : bool} :
  doors_o_callee ω bool (IsOpen d) opened ->
  sel d ω = opened.
Proof. by []. Qed.

(* doors_c => {{door_caller}} p%step {{door_callee}} *)
Definition doors_c : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.
(* -------------------------------------------------------------------------- *)

Local Open Scope classical_set_scope.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : ~~ sel d ω \/ ~~ sel (co d) ω) :
  forall d', ~~ sel d' ω \/ ~~ sel (co d') ω.
Proof.
by move: d safe=> + /[swap]; case; case=> //=; rewrite or_comm.
Qed.

Definition doors_safe (ω : Ω) := ~~ sel left ω \/ ~~ sel right ω.

Section RespectfulAndRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.
Implicit Type d : door.

Local Notation "c ||> p" :=
  (to_hoare (M := M) c p)
  (at level 50, no associativity).

(** Closing a door [d] in any system [ω] is always a respectful operation. *)
Lemma close_door_respectful d : pre (doors_c ||> close_door d) = [set: _].
Proof.
rewrite /close_door -subTset=> hω _; apply: pre_to_hoare_bind.
  by rewrite to_hoare_triggerE /= provided_callerP.
case=> w'; rewrite pre_to_hoare_whenP // !to_hoare_triggerE.
case=> ->.
by apply: provided_bind_caller=> /=.
Qed.

Lemma open_door_respectful (ω : Ω) d (safe : ~~ sel (co d) ω) :
  pre (doors_c ||> open_door d) ω.
Proof.
rewrite /open_door; apply: pre_to_hoare_bind.
  by rewrite to_hoare_triggerE /= provided_callerP.
case=> w'; rewrite pre_to_hoare_whenP // !to_hoare_triggerE.
case=> ->.
by apply: provided_bind_caller; move: safe=> /= /negPf ->.
Qed.

Lemma close_door_run (ω : Ω) d (ω' : Ω) (x : unit)
    (run : post (doors_c ||> close_door d) ω x ω') :
  ~~ sel d ω'.
Proof.
move: run; rewrite /close_door post_to_hoare_bindP.
move=> [opened [witness] []].
rewrite post_to_hoare_whenP !to_hoare_triggerE /= provided_calleeP.
move=> [->].
case: opened=> /= [| /[swap] -> ->] // door_open [[]].
rewrite provided_calleeP /= => -[-> _].
by rewrite tog_equ_1 door_open.
Qed.

Opaque close_door.
Opaque open_door.
Opaque Nat.ltb.
Opaque sel.

Lemma doors_trigger_preserves_safe
    {a : Type} (op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  pre (doors_c ||> ptrigger op) ω ->
  post (doors_c ||> ptrigger op) ω x ω' ->
  doors_safe ω -> doors_safe ω'.
Proof.
rewrite to_hoare_triggerE /=.
rewrite /gen_caller_obligation /gen_witness_update /gen_callee_obligation.
case: prj=> [door_op |] /=;
  last by move=> _ [-> _].
move: door_op x; case=> d /= [] caller [-> _] _ //.
apply: (one_door_safe_all_doors_safe (tog d ω) d).
rewrite tog_equ_1 tog_equ_2 negbK.
case other_open: (sel (co d) ω); [left | by right].
by apply: caller; rewrite other_open.
Qed.

Lemma doors_handler_preserves_safe {a : Type} (op : Fx a) :
  preserves_invariant doors_safe (hoare_of_contract doors_c op).
Proof.
move=> witness result witness' hpre hpost.
apply: doors_trigger_preserves_safe;
  rewrite to_hoare_triggerE.
- exact: hpre.
- exact: hpost.
Qed.
End RespectfulAndRunLemmas.

(* From now on, proofs will use the inductive version. *)
Section InvariantRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : inductiveFreerMonad Fx}.

(** /!\ WARNING: This lemma is the only one needing `f_ind` because we
  * require to "execute" the freer program in order to denote it and see
  * if the invariant was preserved all along.
  *)
Lemma doors_run_preserves_safe {A : Type} (p : M A) :
  preserves_invariant doors_safe (doors_c |> p).
Proof.
by apply: to_hoare_preserves_invariant=> *;
  exact: (doors_handler_preserves_safe (M := M)).
Qed.

Lemma respectful_run_inv {A : Type} (p : M A)
    (ω : Ω) (safe : doors_safe ω)
    (a : A) (ω' : Ω)
    (hpre : pre (doors_c |> p) ω)
    (hpost : post (doors_c |> p) ω a ω') :
  doors_safe ω'.
Proof.
by move: hpre hpost safe; exact: doors_run_preserves_safe.
Qed.
End InvariantRunLemmas.

(** ** Main Theorem *)
Section controller_s.
Context {Fx : effect} `{StrictProvide2 Fx DOORS (STORE nat)}
  {M : inductiveFreerMonad Fx}.

Lemma controller_pre {α : Type} (op : CONTROLLER α) (ω : Ω) :
  pre (doors_c |> controller (M := M) α op) ω.
Proof.
case: op=> [| d].
- (* Tick *) apply: pre_to_hoare_bind.
  + by rewrite to_hoare_triggerE;
      exact: (distinguished_caller (F := DOORS) (G := STORE nat)).
  + move=> cpt witness'.
    rewrite !to_hoare_triggerE.
    move/(distinguished_callee (F := DOORS) (G := STORE nat))=> ->.
    rewrite pre_to_hoare_whenP;
      case: (15 <? cpt)%nat=> //=;
      apply: pre_to_hoare_bind=>[| *].
    * by apply: pre_to_hoare_bind=> [| *];
        rewrite close_door_respectful.
    * by rewrite to_hoare_triggerE;
        exact: (distinguished_caller (F := DOORS) (G := STORE nat)).
- (* Trigger Open *) apply: pre_to_hoare_bind=> [| *].
  + apply: pre_to_hoare_bind=> [| ?? close_post].
    * by rewrite close_door_respectful.
    * exact/open_door_respectful/close_door_run/close_post.
  + by rewrite to_hoare_triggerE;
      exact: (distinguished_caller (F := DOORS) (G := STORE nat)).
Qed.

Theorem controller_correct :
  correct_component controller (M := M)
    (no_contract CONTROLLER) doors_c (fun _ => doors_safe).
Proof.
move=> ? ω ? ? op _; split=> [| ? ? hpost].
  exact: controller_pre.
split=> //.
have hpre := controller_pre op ω; move: hpre hpost.
exact: respectful_run_inv.
Qed.

End controller_s.
