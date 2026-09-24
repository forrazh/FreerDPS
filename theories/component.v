(* This Source Code Fiorm is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import init effect freer contract hoare hoare_lib.
From monae Require Import hierarchy.

(** * Definition *)

(** In FireeSpec, a _component_ is an entity which exposes an effect [Fi],
    and uses primitives of an effect [Fo] to compute the results of primitives
    of [Fi].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                           Fi +-------------------+      Fo
                           | |                   |      |
                   +------>| | c : component Fi Fo |----->|
                           | |                   |      |
                             +-------------------+
>>

    Thus, a component [c : component Fi Fo] is a polymorphic function which
    maps primitives of [Fi] to impure computations using [Fo]. *)

Definition component (Fi Fo : effect) `{M : freerMonad Fo} : Type :=
  Fi ~~> M.

Definition correct_component {Fx Fi Fo : effect} `{Fo -<? Fx}
  {M : freerMonad Fx} (cmp : component Fi Fx)
  {SFi SFo} (cFi : contract Fi SFi) (cFo : contract Fo SFo)
  (r : SFi -> SFo -> Prop) : Prop :=
forall (sFi : SFi) (sFo : SFo) T (cmd : Fi T),
  r sFi sFo -> requirement cFi sFi cmd ->
  pre (cFo |> cmp T cmd) sFo /\
  forall (t : T) (sFo' : SFo),
    post (cFo |> (cmp T cmd : M _)) sFo t sFo' ->
    promise cFi sFi cmd t /\
    r (state_update cFi sFi cmd t) sFo'.
