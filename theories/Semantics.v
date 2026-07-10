(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

Attributes deprecated(
  note="This file is unused and will probably be removed in later versions.").

(** In FreeSpec, there is no particular semantics attach to effect's
    primitives. Once an effect has been defined, we can provide one (or
    more) operational semantics to interpret its primitives. *)

(** * Definition *)

(** An operational [semantics] for the effect [F] is coinductively defined as
    a function which can be used to interpret any primitive of [F]; it produces
    an [interp_out] term. *)

From FreerDPS Require Import Init.
(* From ExtLib Require Import Monad StateMonad. *)
From FreerDPS Require Export Effect Freer.
From monae Require Import monad_model.

#[local] Open Scope signature_scope.
#[local] Open Scope monae_scope.


CoInductive semantics (F : effect) : Type :=
| mk_semantics (f : forall (α : Type), F α -> α * semantics F) : semantics F.

Arguments mk_semantics [F] (f).

(** Thus, a [semantics] does not only compute a result for a primitive, but also
    provides a new semantics.  This is necessary to model impurity: the same
    primitive may or may not return the same result when called several
    times.

    As for effects, the simpler [semantics] is the operational semantics for
    [eempty], the empty effect. *)

Definition eempty_semantics : semantics eempty :=
  mk_semantics (fun α (op : eempty α) => match op with end).

(** We also provide a semantics for the [STORE s] effect: *)

CoFixpoint store {s} (init : s) : semantics (STORE s) :=
  mk_semantics (fun α (op : STORE s α) =>
                  match op with
                  | Get => (init, store init)
                  | Put next => (tt, store next)
                  end).

(** We provide several helper functions to interpret primitives with
    semantics. *)

Definition run_effect {F α} (sem : semantics F) (op : F α) : α * semantics F :=
  match sem with mk_semantics f => f α op end.

Definition eval_effect {F α} (sem : semantics F) (op : F α) : α :=
  fst (run_effect sem op).

Definition exec_effect {F α} (sem : semantics F) (op : F α) : semantics F :=
  snd (run_effect sem op).

Lemma run_effect_equation {F α} (sem : semantics F) (op : F α)
  : run_effect sem op = (eval_effect sem op, exec_effect sem op).

Proof.
  unfold eval_effect, exec_effect.
  destruct run_effect; reflexivity.
Qed.

(** Besides, and similarly to effects, operational semantics can and should
    be composed together.  To that end, we provide the [semprod] operator. *)

CoFixpoint semprod {F E} (semF : semantics F) (semE : semantics E)
  : semantics (F + E) :=
  mk_semantics (fun _ op =>
                  match op with
                  | in_left op =>
                    let (x, out) := run_effect semF op in
                    (x, semprod out semE)
                  | in_right op =>
                    let (x, out) := run_effect semE op in
                    (x, semprod semF out)
                  end).

Declare Scope semantics_scope.
Bind Scope semantics_scope with semantics.
Delimit Scope semantics_scope with semantics.

Infix "*" := semprod : semantics_scope.

(** * Interpreting Impure Computations *)

(** A term of type [freer F a] describes an impure computation expected to
    return
    a term of type [a].  Interpreting this term means actually realizing the
    computation and producing the result.  This requires to provide an
    operational semantics for the effects used by the computation.

    Some operational semantics may be defined in Gallina by means of the
    [semantics] type. In such a case, we provide helper functions to use them in
    conjunction with [freer] terms. The terminology follows a logic similar to
    the Haskell state monad:

    - [run_impure] interprets an impure computation [p] with an operational
      semantics [sem], and returns both the result of [p] and the new
      operational semantics to use afterwards.
    - [eval_impure] only returns the result of [p].
    - [exec_impure] only returns the new operational semantics. *)

Notation interp F := (StateMonad.acto (semantics F)).

Definition effect_to_state {F : effect} : F ~~> interp F :=
  fun _ op sem => run_effect sem op.


Definition to_state {F} {im : freerMonad F} : im ~~> interp F :=
  denote _ effect_to_state.

Arguments to_state {F α} _ : rename.
Arguments to_state {F α} _ : rename.

Definition run_impure {F a} {im : freerMonad F}
    (sem : semantics F) (p : im a) : a * semantics F :=
  (to_state _ p) sem.

Definition eval_impure {F a} {im : freerMonad F}
    (sem : semantics F) (p : im a) : a :=
  fst (run_impure sem p).

Definition exec_impure {F a} {im : freerMonad F}
    (sem : semantics F) (p : im a) : semantics F :=
  snd (run_impure sem p).

(** * In-place Primitives Handling *)


Fixpoint with_semantics {Fx E α}
    (sem : semantics E) (p : freer (Fx + E) α)
  : freer Fx α :=
  match p with
  | pure x => pure x
  | impure _ (in_right op) k =>
    let (res, next) := run_effect sem op in
    with_semantics next (k res)
  | impure _ (in_left op) k =>
    impure op (fun x => with_semantics sem (k x))
  end.

(** We provide [with_store], a helper function to locally provide a mutable
    variable. *)

Definition with_store {Fx s a} (x : s) (p : freer (Fx + STORE s) a)
  : freer Fx a :=
  with_semantics (store x) p.

(** Nesting [with_semantics] calls works to some extends. If each
    [with_semantics] provides a different effect from the rest of the stack,
    then everything behaves as expected. If, for some reason, you end up in a
    situation where you provide the exact same effect twice (typically if you
    use [with_store]), then the typeclass inferences will favor the deepest one
    in the stack. For instance,

<<
Compute (with_store 0 (with_store 1 get)).
>>

    returns

<<
     = pure 1
     : freer ?Fx nat
>> *)
