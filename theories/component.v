(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import init effect freer contract hoare_lib.

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
  forall (α : Type), F α -> M α.

Definition correct_component {Ex E F : effect} `{E -<? Ex} {M : freerMonad Ex}
  {ΩF ΩE : Type}
    (c : component F Ex) (cF : contract F ΩF)
    (cE : contract E ΩE) (pred : ΩF -> ΩE -> Prop) :
  Prop :=
  forall (ωF : ΩF) (ωE : ΩE) (init : pred ωF ωE) (α : Type)
      (op : F α) (o_caller : requirement cF ωF op),
    pre (cE |> c α op) ωE /\
    forall (x : α) (ωE' : ΩE),
      post (cE |> (c α op : M _)) ωE x ωE' ->
      promise cF ωF op x /\
      pred (state_update cF ωF op x) ωE'.
