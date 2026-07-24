(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

Attributes deprecated(
  note="This file is unused and will probably be removed in later versions.").

From FreerDPS Require Import Init.
(* From ExtLib Require Import StateMonad. *)
From FreerDPS Require Export Effect Semantics Freer.
From monae Require Import monad_lib.
(** * Definition *)

(** In FreeSpec, a _component_ is an entity which exposes an effect [F],
    and uses primitives of an effect [E] to compute the results of primitives
    of [F].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                           F +-------------------+      E
                           | |                   |      |
                   +------>| | c : component F E |----->|
                           | |                   |      |
                             +-------------------+
>>

    Thus, a component [c : component F E] is a polymorphic function which
    maps primitives of [F] to impure computations using [E]. *)

Definition component (F E : effect) `{im : impureMonad E} : Type :=
  forall (α : Type), F α -> im α.

(** The similarity between FreeSpec components and operational semantics may be
    confusing at first. The main difference between the two concepts is simple:
    operational semantics are self-contained terms which can, alone, be used to
    interpret impure computations of a given effect.  Components, on the
    other hand, are not self-contained.  Without an operational semantics for
    [E], we cannot use a component [c : component F E] to interpret an impure
    computation using [F].

    Given an initial semantics for [E], we can however derive an operational
    semantics for [F] from a component [c]. *)

(** * Semantics Derivation *)


CoFixpoint derive_semantics {F E} {im : impureMonad E} (c : component F E) (sem : semantics E)
  : semantics F :=
  mk_semantics (fun a p =>
                  let (res, next) := (to_state (α:=im) _ $ c a p) sem in
                  (res, derive_semantics c next)).

(** So, [semprod] on the one hand allows for composing operational semantics
    horizontally, and [derive_semantics] allows for composing components
    vertically.  Using these two operators, we can model a complete system in a
    hierarchical and modular manner, by defining each of its components
    independently, then composing them together with [semprod] and
    [derive_semantics]. *)

Definition bootstrap {F} {im : impureMonad eempty}
    (c : component F eempty) : semantics F :=
  derive_semantics (im:=im) c eempty_semantics.

(** * In-place Primitives Handling *)

(** The function [with_component] allows for locally providing an additional
    effect [E] within an impure computation of type [impure Fx a]. The
    primitives of [E] will be handled by impure computations, i.e., a component.
    of type [c : compoment E Fx s]. *)
Local Open Scope monae_scope.


#[local]
Fixpoint with_component_aux {Fx E α}
 (* {im : impureMonad Fx}  *)
 (* {jm : impureMonad (Fx + E)} *)
(c : component
       (im:=Freer.Impure.ImpureModule_acto__canonical__Freer_MonadImpure Fx)
       E Fx)
    (p : impure (Fx + E) α)
  : impure Fx α :=
  match p with
  | local x => local x
  | request_then T (in_right e) f =>
    c T e >>= fun res => with_component_aux c (f res)
  | request_then _ (in_left e) f =>
    request_then e (fun x => with_component_aux c (f x))
  end.

Notation "m >>= f" := (impure_bind m f).
Notation "m >> f" := (impure_bind m (fun _ =>f)).

Definition with_component {Fx E α}
  (* `{im : impureMonad Fx}
  `{ixjm : impureMonad (Fx+E)} *)
  (initializer : impure Fx unit)
  (c : component
         (im:=Freer.Impure.ImpureModule_acto__canonical__Freer_MonadImpure Fx)
         E Fx)
  (finalizer : impure Fx unit)
  (p : impure (Fx+E) α)
  : impure Fx α :=
  initializer >>
  with_component_aux c p >>= fun res =>
  finalizer >>
  local res.
