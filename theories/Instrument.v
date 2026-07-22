(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

Attributes deprecated(
  note="This file is unused and will probably be removed in later versions.").

From FreerDPS Require Import Interface Semantics Contract.
From monae Require Import preamble hierarchy monad_transformer monad_model.
From HB Require Import structures.

From mathcomp Require Import ssreflect.
Generalizable All Variables.

Notation instrument Ω i := (stateT Ω (StateMonad.acto (semantics i))).


Definition modify {S} {M : stateMonad S} (f : S -> S) : M S := get >>= 
  fun s => put (f s) >>=
  fun _ => Ret s.

Arguments liftS {_ _ _}.
Arguments interface_to_state {_ _}.


Program Definition interface_to_instrument `{MayProvide ix i} `(c : contract i Ω)
  : ix ~~> instrument Ω ix := 
  fun a e => 
    (liftS (A:=a) $ interface_to_state e) 
    >>= fun x => modify (fun ω => gen_witness_update c ω e x)
    >>= fun _ => Ret x.

Definition to_instrument `{MayProvide ix i} `(c : contract i Ω) {im : impureMonad ix}
  : im ~~> instrument Ω ix :=
  impure_lift _ $ interface_to_instrument c.

Arguments to_instrument {ix i _ Ω} (c) {α} : rename.

