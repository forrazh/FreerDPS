(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** * Utils Functions *)
From monae Require Import hierarchy.

Global Close Scope nat_scope.
Global Open Scope monae_scope.

(* TODO: Check if this is already in monae *)
Definition when {X} {M : monad}  (b : bool) (m : M X) : M unit :=
  if b then m >> skip else skip.
Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Reserved Infix "===" (at level 70, no associativity).

Set Typeclasses Strict Resolution.
