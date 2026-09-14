(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra init effect freer hoare.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Weakest preconditions

    Reference: Benjamin Lucien Kaminski,
    Advanced Weakest Precondition Calculi for Probabilistic Programs.
    PhD thesis, RWTH Aachen University, 2018, Chapter 2.
    https://discovery.ucl.ac.uk/id/eprint/10089706/

    PDF: https://discovery.ucl.ac.uk/id/eprint/10089706/1/blk-diss.version-2018-10-26-druckversion-ohne-bild.pdf
*)
