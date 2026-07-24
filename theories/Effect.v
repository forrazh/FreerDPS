(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import Init.

(** * Definition  *)

(** Following the definition of the <<operational>> package, effects in
    FreeSpec are parameterized inductive types whose terms purposely describe
    the primitives the effect provides. *)

Definition effect := Type -> Type.

Declare Scope effect_scope.
Bind Scope effect_scope with effect.

(** Given [F : effect], a term of type [F α] identifies a primitive of [F]
    expected to produce a result of type [α].

    The simpler effect is the empty effect, which provides no primitives
    whatsoever. *)

Inductive eempty : effect := .

(** Another example of general-purpose effect we can define is the [STORE s]
    effect, where [s] is a type for a state, and [STORE s] allows for
    manipulating a global, mutable variable of type [s] within an impure
    computation. *)

Inductive STORE (s : Type) : effect :=
| Get : STORE s s
| Put (x : s) : STORE s unit.

Arguments Get {s}.
Arguments Put [s] (x).

(** According to the definition of [STORE s], an impure computation can use two
    primitives. The term [Get : STORE s s] describes a primitive expected to
    produce a result of type [s], that is the current value of the mutable
    variable.  Terms of the form [Put x : STORE s unit] describe a primitive
    which does not produce any meaningful result, but is expected to update the
    current value of the mutable variable.

    The use of the word “expected” to describe the primitive of [STORE s] is
    voluntary.  The definition of an effect does not attach any particular
    semantics to the primitives it describes.  This will come later, and in
    fact, one effect may have many legitimate semantics.

    Impure computations are likely to use more than one effect, but the
    [impure] monad takes only one argument.  We introduce [eplus] (denoted by
    [<+>] or [⊕]) to compose effects together.  An impure computation
    parameterized by [F ⊕ E] can therefore leverage the primitives of both [F]
    and [E]. *)

(** * Polymorphic Effect Composites *)

(** When defining general-purpose impure computations that we expect to reuse in
    different context, we want to leave the effect as a parameter, and rather
    express the constraints in terms of effect availability.  We tackle this
    challenge by means of _effect composites_.

    - We say an effect composite [ix] _provides_ a concrete effect [i]
      when there exists a function [inj_p : forall α, i α -> ix α].
    - Conversely, we can determine if a primitive of an effect composite [ix]
      is forwarded to a concrete effect [i] when there exists a function
      [proj_p : forall α, ix α -> option (i a)].

    We encode this mechanics using two type classes: [MayProvide], and
    [Provide]. *)

Class MayProvide (ix i : effect) : Type :=
  { proj_p {α} (e : ix α) : option (i α)
  }.

Class Provide (ix i : effect) `{MayProvide ix i} : Type :=
  { inj_p {α} (e : i α) : ix α
  ; proj_inj_p_equ {α} (e : i α) : proj_p (inj_p e) = Some e
  }.

(** We provide a default instance for [MayProvide] in the form of a function
    [proj_p] which always return [None].  We give to this default instance a
    ridiculously high priority number to ensure it is selected only if no other
    instances are found. *)

Instance default_MayProvide (i j : effect) : MayProvide i j|1000 :=
  { proj_p := fun _ _ => None
  }.

(** It is expected that, for an effect composite [ix] which provides [i] and
    may provide [j], [inj_p] and [proj_p] do not mix up [i] and [j]
    primitives. That is, injecting a primitive [e] of [i] inside [ix], then
    projecting the resulting primitive into [j] returns [None] as long as [i]
    and [j] are two different effects. *)

Class Distinguish (ix i j : effect) `{Provide ix i, MayProvide ix j} : Prop :=
  { distinguish : forall {α} (e : i α), proj_p (i := j) (inj_p (ix := ix) e) = None
  }.

(** * Composing Effects *)

(** We provide the [eplus] operator to compose effects together. That is,
    [eplus] can be used to build _concrete_ (as opposed to polymorphic)
    effect composite. *)

Inductive eplus (i j : effect) (α : Type) :=
| in_left (e : i α) : eplus i j α
| in_right (e : j α) : eplus i j α.

Arguments in_left [i j α] (e).
Arguments in_right [i j α] (e).

Register eplus as freespec.core.eplus.type.
Register in_left as freespec.core.eplus.in_left.
Register in_right as freespec.core.eplus.in_right.

Infix "+" := eplus : effect_scope.

(** For [eplus] to be used seamlessly as a concrete effect composite, we
    provide the necessary instances for the [MayProvide], [Provide] and
    [Distinguish] type classes. Note that these instances always prefer the
    left operand of [eplus]. For instance, considering a situation where
    there is an instance for [Provide ix i] and an instance for [Provide jx i],
    the instance of [Provide (ix + jx) i] will rely on [ix].

    The main use case for [eplus] is to locally provide an additional
    effect. For instance, we can consider a [with_state] function which would
    locally give access to the [STORE] effect, that is [with_state : forall
    ix s α, s -> impure (ix + STORE s) α -> impure ix α]. In such a case, the
    effect made locally available shall be the right operand of [eplus]. This
    way, functions such as [with_state] are reentrant. If we take an example,
    the following impure computation:

<<
with_state true (with_state false get)
>>

    will return false (that is, the variable in the inner store). *)

Instance refl_MayProvide (i : effect) : MayProvide i i :=
  { proj_p := fun _ e => Some e
  }.

#[program]
Instance refl_Provide (i : effect) : @Provide i i (refl_MayProvide i) :=
  { inj_p := fun (a : Type) (e : i a) => e
  }.

Instance eplus_left_MayProvide (ix i j : effect) `{MayProvide ix i}
  : MayProvide (ix + j) i :=
  { proj_p := fun _ e =>
                match e with
                | in_left e => proj_p e
                | _ => None
                end
  }.

#[program]
Instance eplus_left_Provide (ix i j : effect) `{Provide ix i}
  : @Provide (ix + j) i (eplus_left_MayProvide ix i j) :=
  { inj_p := fun (a : Type) (e : i a) => in_left (inj_p e)
  }.

Next Obligation.
  now rewrite proj_inj_p_equ.
Qed.

Instance eplus_right_MayProvide (i jx j : effect) `{MayProvide jx j}
  : MayProvide (i + jx) j :=
  { proj_p := fun _ e =>
                match e with
                | in_right e => proj_p e
                | _ => None
                end
  }.

#[program]
Instance eplus_right_Provide (i jx j : effect) `{Provide jx j}
  : @Provide (i + jx) j (eplus_right_MayProvide i jx j) :=
  { inj_p := fun _ e => in_right (inj_p e)
  }.

Next Obligation.
  now rewrite proj_inj_p_equ.
Qed.

(** By default, Coq's inference algorithm for type classe instances inference is
    a depth-first search. This is not without consequence in our case. For
    instance, if we consider the search of an instance for [MayProvide (i + j)
    j], Coq will first try [eplus_right_MayProvide] (as explained previously),
    meaning he now search for [MayProvide i j]. It turns out such an instance
    exists: [default_MayProvide].

    To circumvent this issue, we write a dedicated tactic [find_may_provide]
    which attempts to find an instance for [MayProvide (?ix + ?jx) ?i] with
    [refl_MayProvide], [eplus_left_MayProvide] and [eplus_right_MayProvide]. *)

Ltac find_may_provide :=
  eapply refl_MayProvide +
  (eapply eplus_left_MayProvide; find_may_provide) +
  (eapply eplus_right_MayProvide; find_may_provide).

#[global] Hint Extern 1 (MayProvide (eplus _ _) _) =>
  find_may_provide : typeclass_instances.

#[program]
Instance refl_Distinguish (i j : effect)
  : @Distinguish i i j  ( @refl_MayProvide i) ( @refl_Provide i) ( @default_MayProvide i j).

#[program]
Instance eplus_left_default_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide ix i} `{P1 : @Provide ix i M1}
  : @Distinguish (ix + jx) i j
                 ( @eplus_left_MayProvide ix i jx M1)
                 ( @eplus_left_Provide ix i jx M1 P1)
                 ( @default_MayProvide _ j).

#[program]
Instance eplus_right_default_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide jx i} `{P1 : @Provide jx i M1}
  : @Distinguish (ix + jx) i j
                 ( @eplus_right_MayProvide ix jx i M1)
                 ( @eplus_right_Provide ix jx i M1 P1)
                 ( @default_MayProvide _ j).

#[program]
Instance eplus_left_may_right_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide ix i} `{P1 : @Provide ix i M1} `{M2 : MayProvide jx j}
  : @Distinguish (ix + jx) i j
                 ( @eplus_left_MayProvide ix i jx M1)
                 ( @eplus_left_Provide ix i jx M1 P1)
                 ( @eplus_right_MayProvide ix jx j M2).

#[program]
Instance eplus_right_may_left_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide jx i} `{P1 : @Provide jx i M1} `{M2 : MayProvide ix j}
  : @Distinguish (ix + jx) i j
                 ( @eplus_right_MayProvide ix jx i M1)
                 ( @eplus_right_Provide ix jx i M1 P1)
                 ( @eplus_left_MayProvide ix j jx M2).

#[program]
Instance eplus_left_distinguish_left_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide ix i} `{P1 : @Provide ix i M1} `{M2 : MayProvide ix j}
   `{@Distinguish ix i j M1 P1 M2}
  : @Distinguish (ix + jx) i j
                 ( @eplus_left_MayProvide ix i jx M1)
                 ( @eplus_left_Provide ix i jx M1 P1)
                 ( @eplus_left_MayProvide ix j jx M2).

Next Obligation.
  apply distinguish.
Defined.

#[program]
Instance eplus_right_distinguish_right_Distinguish (ix jx i j : effect)
   `{M1 : MayProvide jx i} `{P1 : @Provide jx i M1} `{M2 : MayProvide jx j}
   `{@Distinguish jx i j M1 P1 M2}
  : @Distinguish (ix + jx) i j
                 ( @eplus_right_MayProvide ix jx i M1)
                 ( @eplus_right_Provide ix jx i M1 P1)
                 ( @eplus_right_MayProvide ix jx j M2).

Next Obligation.
  apply distinguish.
Defined.
