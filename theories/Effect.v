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
    [freer] monad takes only one argument.  We introduce [eplus] (denoted by
    [<+>] or [⊕]) to compose effects together.  An impure computation
    parameterized by [F ⊕ E] can therefore leverage the primitives of both [F]
    and [E]. *)

Inductive NonDetEff : effect :=
| select_e : NonDetEff bool
.

(** * Polymorphic Effect Composites *)

(** When defining general-purpose impure computations that we expect to reuse in
    different context, we want to leave the effect as a parameter, and rather
    express the constraints in terms of effect availability.  We tackle this
    challenge by means of _effect composites_.

    - We say an effect composite [Fx] _provides_ a concrete effect [F]
      when there exists a function [inj_p : forall α, F α -> Fx α].
    - Conversely, we can determine if a primitive of an effect composite [Fx]
      is forwarded to a concrete effect [F] when there exists a function
      [proj_p : forall α, Fx α -> option (F a)].

    We encode this mechanics using two type classes: [MayProvide], and
    [Provide]. *)

Class MayProvide (Fx F : effect) : Type :=
  { proj_p {α} (op : Fx α) : option (F α)
  }.

Class Provide (Fx F : effect) `{MayProvide Fx F} : Type :=
  { inj_p {α} (op : F α) : Fx α
  ; proj_inj_p_equ {α} (op : F α) : proj_p (inj_p op) = Some op
  }.

(** We provide a default instance for [MayProvide] in the form of a function
    [proj_p] which always return [None].  We give to this default instance a
    ridiculously high priority number to ensure it is selected only if no other
    instances are found. *)

Instance default_MayProvide (F E : effect) : MayProvide F E|1000 :=
  { proj_p := fun _ _ => None
  }.

(** It is expected that, for an effect composite [Fx] which provides [F] and
    may provide [E], [inj_p] and [proj_p] do not mix up [F] and [E]
    primitives. That is, injecting a primitive [op] of [F] inside [Fx], then
    projecting the resulting primitive into [E] returns [None] as long as [F]
    and [E] are two different effects. *)

Class Distinguish (Fx F E : effect) `{Provide Fx F, MayProvide Fx E} : Prop :=
  { distinguish : forall {α} (op : F α),
      proj_p (F := E) (inj_p (Fx := Fx) op) = None
  }.

(** * Composing Effects *)

(** We provide the [eplus] operator to compose effect together. That is,
    [eplus] can be used to build _concrete_ (as opposed to polymorphic)
    effect composite. *)

Inductive eplus (F E : effect) (α : Type) :=
| in_left (op : F α) : eplus F E α
| in_right (op : E α) : eplus F E α.

Arguments in_left [F E α] (op).
Arguments in_right [F E α] (op).

Infix "+" := eplus : effect_scope.

(** For [eplus] to be used seamlessly as a concrete effect composite, we
    provide the necessary instances for the [MayProvide], [Provide] and
    [Distinguish] type classes. Note that these instances always prefer the
    left operand of [eplus]. For instance, considering a situation where
    there is an instance for [Provide Fx F] and an instance for [Provide Ex F],
    the instance of [Provide (Fx + Ex) F] will rely on [Fx].

    The main use case for [eplus] is to locally provide an additional
    effect. For instance, we can consider a [with_state] function which would
    locally give access to the [STORE] effect, that is [with_state : forall
    Fx s α, s -> freer (Fx + STORE s) α -> freer Fx α]. In such a case, the
    effect made locally available shall be the right operand of [eplus]. This
    way, functions such as [with_state] are reentrant. If we take an example,
    the following impure computation:

<<
with_state true (with_state false get)
>>

    will return false (that is, the variable in the inner store). *)

Instance refl_MayProvide (F : effect) : MayProvide F F :=
  { proj_p := fun _ op => Some op
  }.

#[program]
Instance refl_Provide (F : effect) : @Provide F F (refl_MayProvide F) :=
  { inj_p := fun (a : Type) (op : F a) => op
  }.

Instance eplus_left_MayProvide (Fx F E : effect) `{MayProvide Fx F}
  : MayProvide (Fx + E) F :=
  { proj_p := fun _ op =>
                match op with
                | in_left op => proj_p op
                | _ => None
                end
  }.

#[program]
Instance eplus_left_Provide (Fx F E : effect) `{Provide Fx F}
  : @Provide (Fx + E) F (eplus_left_MayProvide Fx F E) :=
  { inj_p := fun (a : Type) (op : F a) => in_left (inj_p op)
  }.

Next Obligation.
  now rewrite proj_inj_p_equ.
Qed.

Instance eplus_right_MayProvide (F Ex E : effect) `{MayProvide Ex E}
  : MayProvide (F + Ex) E :=
  { proj_p := fun _ op =>
                match op with
                | in_right op => proj_p op
                | _ => None
                end
  }.

#[program]
Instance eplus_right_Provide (F Ex E : effect) `{Provide Ex E}
  : @Provide (F + Ex) E (eplus_right_MayProvide F Ex E) :=
  { inj_p := fun _ op => in_right (inj_p op)
  }.

Next Obligation.
  now rewrite proj_inj_p_equ.
Qed.

(** By default, Coq's inference algorithm for type classe instances inference is
    a depth-first search. This is not without consequence in our case. For
    instance, if we consider the search of an instance for [MayProvide (F + E)
    E], Coq will first try [eplus_right_MayProvide] (as explained previously),
    meaning he now search for [MayProvide F E]. It turns out such an instance
    exists: [default_MayProvide].

    To circumvent this issue, we write a dedicated tactic [find_may_provide]
    which attempts to find an instance for [MayProvide (?Fx + ?Ex) ?F] with
    [refl_MayProvide], [eplus_left_MayProvide] and [eplus_right_MayProvide]. *)

Ltac find_may_provide :=
  eapply refl_MayProvide +
  (eapply eplus_left_MayProvide; find_may_provide) +
  (eapply eplus_right_MayProvide; find_may_provide).

#[global] Hint Extern 1 (MayProvide (eplus _ _) _) =>
  find_may_provide : typeclass_instances.

#[program]
Instance refl_Distinguish (F E : effect)
  : @Distinguish F F E (@refl_MayProvide F) (@refl_Provide F)
      (@default_MayProvide F E).

#[program]
Instance eplus_left_default_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Fx F} `{P1 : @Provide Fx F M1}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_left_MayProvide Fx F Ex M1)
                 ( @eplus_left_Provide Fx F Ex M1 P1)
                 ( @default_MayProvide _ E).

#[program]
Instance eplus_right_default_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Ex F} `{P1 : @Provide Ex F M1}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_right_MayProvide Fx Ex F M1)
                 ( @eplus_right_Provide Fx Ex F M1 P1)
                 ( @default_MayProvide _ E).

#[program]
Instance eplus_left_may_right_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Fx F} `{P1 : @Provide Fx F M1} `{M2 : MayProvide Ex E}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_left_MayProvide Fx F Ex M1)
                 ( @eplus_left_Provide Fx F Ex M1 P1)
                 ( @eplus_right_MayProvide Fx Ex E M2).

#[program]
Instance eplus_right_may_left_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Ex F} `{P1 : @Provide Ex F M1} `{M2 : MayProvide Fx E}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_right_MayProvide Fx Ex F M1)
                 ( @eplus_right_Provide Fx Ex F M1 P1)
                 ( @eplus_left_MayProvide Fx E Ex M2).

#[program]
Instance eplus_left_distinguish_left_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Fx F} `{P1 : @Provide Fx F M1} `{M2 : MayProvide Fx E}
   `{@Distinguish Fx F E M1 P1 M2}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_left_MayProvide Fx F Ex M1)
                 ( @eplus_left_Provide Fx F Ex M1 P1)
                 ( @eplus_left_MayProvide Fx E Ex M2).

Next Obligation.
  apply distinguish.
Defined.

#[program]
Instance eplus_right_distinguish_right_Distinguish (Fx Ex F E : effect)
   `{M1 : MayProvide Ex F} `{P1 : @Provide Ex F M1} `{M2 : MayProvide Ex E}
   `{@Distinguish Ex F E M1 P1 M2}
  : @Distinguish (Fx + Ex) F E
                 ( @eplus_right_MayProvide Fx Ex F M1)
                 ( @eplus_right_Provide Fx Ex F M1 P1)
                 ( @eplus_right_MayProvide Fx Ex E M2).

Next Obligation.
  apply distinguish.
Defined.
