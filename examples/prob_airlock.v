(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From Stdlib Require Import Arith.
From FreerDPS Require Import Core Impure Hoare.
From monae Require Import preamble hierarchy.

From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct.
From infotheo Require Import realType_ext ssr_ext fsdist convex.
#[local] Open Scope nat_scope.
#[local] Open Scope monae_scope.
#[local] Open Scope proba_scope.
Local Open Scope reals_ext_scope.



Create HintDb airlock.



Import ProbIfaceMod.

Inductive door : Type := left | right.

Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.



Check request.

Section a.

    Context (R : realType).

Definition is_open `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im bool := trigger (inj_p $ IsOpen d).

Definition toggle `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im unit := trigger (inj_p $ Toggle d).

Definition open_door `{Provide2 ix DOORS prob_interface} {im : impureMonad ix} (d : door) (p : {prob R}) : im unit :=
    can_work p >>= fun ok => when ok $
        is_open d >>= fun open =>
        when (negb open) (toggle d).

Definition close_door `{Provide2 ix DOORS prob_interface} {im : impureMonad ix} (d : door) (p: {prob R}): im unit :=
    can_work p >>= fun ok => when ok $
        is_open d >>= fun open =>
        when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} {im : impureMonad ix} : im unit :=
  trigger (inj_p Tick).

Definition request_open `{Provide ix CONTROLLER} {im : impureMonad ix}  (d : door) : im unit :=
  trigger (inj_p $ RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Check (forall i, component CONTROLLER i).

Search iget.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat), Provide ix prob_interface} {im : impureMonad ix}
  : {prob R} -> component (im:=im) CONTROLLER ix
  (* .
  move=>X; case=>[|d].
  - apply/bind=>[|cpt].
    + apply/iget.
    + apply/when.
      * apply: (15 <? cpt).
      * apply/bind=>[|_].
      -- apply/close_door/left.
      -- apply/bind=>[|_].
        ++ apply/close_door/right.
        ++ apply/iput/0.
  - apply/bind=>[|_].
    + apply/close_door/co/d.
    + apply/bind=>[|_].
      * apply/open_door/d.
      * apply/iput/0.
  Show Proof. *)
   := 
  fun p _ op =>
    match op with
    | Tick =>
      iget >>= fun cpt =>
      when (15 <? cpt) $
        close_door left p >>
        close_door right p >>
        iput 0
    | RequestOpen d =>
        close_door (co d) p >>
        open_door d p >>
        iput 0
    end.

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(** *** Witness States *)

Definition Ω : Type := bool * bool.

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = negb (sel d ω).

Proof.
  by case:d.
Qed.

Lemma tog_equ_2 (d : door) (ω : Ω)
  : sel (co d) (tog d ω) = sel (co d) ω.

Proof.
  destruct d; reflexivity.
Qed.

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

#[local] Opaque tog.

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.
