(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import init effect freer contract hoare.
From monae Require Import hierarchy.

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

Definition component (F E : effect) `{M : freerMonad E} : Type :=
  F ~~> M.

Definition correct_component {Ex E F : effect} `{E -<? Ex} {M : freerMonad Ex}
  {SF SE : Type}
    (c : component F Ex) (cF : contract F SF)
    (cE : contract E SE) (pred : SF -> SE -> Prop) :
  Prop :=
  forall (sF : SF) (sE : SE) (init : pred sF sE) (T : Type)
      (cmd : F T) (o_caller : requirement cF sF cmd),
    pre (cE |> c T cmd) sE /\
    forall (x : T) (sE' : SE),
      post (cE |> (c T cmd : M _)) sE x sE' ->
      promise cF sF cmd x /\
      pred (state_update cF sF cmd x) sE'.
