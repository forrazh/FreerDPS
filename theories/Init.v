(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** * Utils Functions *)
(* From HB Require Export structures. *)
From monae Require Export preamble hierarchy.
From mathcomp Require Export ssreflect. 
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | simple refine (@sym_equal _ _ _ _); trivial]
         | discriminate | contradiction | split]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end 
   | auto with freespec
   ].
Local Open Scope monae_scope.

Definition when {X} {M : monad}  (b : bool) (m : M X) : M unit := if b then m >> skip else skip. 
Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

(** * Tactics *)

From Stdlib Require Export Eqdep.

Ltac ssubst :=
  lazymatch goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ]
  => apply Eqdep.EqdepTheory.inj_pair2 in H; ssubst
| [ |- _] => subst
end.

Reserved Infix "===" (at level 70, no associativity).
 
Generalizable All Variables.

Definition function_eq {a b} (r : b -> b -> Prop) (f g : a -> b) : Prop :=
  forall (x : a), r (f x) (g x).
