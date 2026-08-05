(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From mathcomp Require Import ssreflect ssrfun.
From monae Require Import hierarchy.
From Stdlib Require Import Program.

Local Open Scope monae_scope.

(** * Definition  *)

(** Following the definition of the <<operational>> package, effs in
    FreeSpec are parameterized inductive types whose terms purposely describe
    the primitives the eff provides. *)

Definition eff := Type -> Type.

Declare Scope eff_scope.
Bind Scope eff_scope with eff.

(** Given [F : eff], a term of type [F α] identifies a primitive of [F]
    expected to produce a result of type [α].

    The simpler eff is the empty eff, which provides no primitives
    whatsoever. *)

Inductive eempty : eff := .

(** Another example of general-purpose eff we can define is the [STORE s]
    eff, where [s] is a type for a state, and [STORE s] allows for
    manipulating a global, mutable variable of type [s] within an impure
    computation. *)

Inductive STORE (s : Type) : eff :=
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
    voluntary.  The definition of an eff does not attach any particular
    semantics to the primitives it describes.  This will come later, and in
    fact, one eff may have many legitimate semantics.

    Impure computations are likely to use more than one eff, but the
    [freer] monad takes only one argument.  We introduce [eplus] (denoted by
    [<+>] or [⊕]) to compose effs together.  An impure computation
    parameterized by [F ⊕ E] can therefore leverage the primitives of both [F]
    and [E]. *)

(** * Polymorphic Effect Composites *)
Class MayProvide (Fx F : eff) : Type :=
  { prj: Fx ~~> option \o F (* retraction *)
  }.
Arguments prj {_ _ _ _} _.

Notation "F -<? Fx" := (MayProvide Fx F)
  (at level 92, left associativity) : type_scope.

Class Provide (Fx F : eff) : Type :=
  { may_prov :: F -<? Fx ;
    inj : F ~~> Fx (* section *);
    injK_Some {A} : forall e : F A, may_prov.(prj) (inj _ e) = Some e }.
Arguments inj {_ _ _ _} _.

Notation "F -< Fx" := (Provide Fx F)
  (at level 92, left associativity) : type_scope.

(** We provide a default instance for [MayProvide] in the form of a function
    [prj] which always return [None].  We give to this default instance a
    ridiculously high priority number to ensure it is selected only if no other
    instances are found. *)

Instance default_MayProvide (F E : eff) : (E -<? F) |1000 :=
  { prj := fun _ _ => None }.

(** It is expected that, for an eff composite [Fx] which provides [F] and
    may provide [E], [inj] and [prj] do not mix up [F] and [E]
    primitives. That is, injecting a primitive [e] of [F] inside [Fx], then
    prjecting the resulting primitive into [E] returns [None] as long as [F]
    and [E] are two different effs. *)

Class Distinguish (Fx F E : eff) `{Hp: F -< Fx, Hmp : E -<? Fx} : Prop :=
  {
    injK_None : forall {A} (e: F A), Hmp.(prj) (Hp.(inj) e) = None
  }.
(* @prj Fx E H1 A (@inj Fx F H H0 A e) *)
(* F -< Fx
Subev -< Ev *)

(** * Composing Effects *)

(** We provide the [eplus] operator to compose effs together. That is,
    [eplus] can be used to build _concrete_ (as opposed to polymorphic)
    eff composite. *)


Inductive eplus (F E : eff) (α : Type) :=
| in_left (e : F α) : eplus F E α
| in_right (e : E α) : eplus F E α.

Arguments in_left [F E α] (e).
Arguments in_right [F E α] (e).

Register eplus as freespec.core.eplus.type.
Register in_left as freespec.core.eplus.in_left.
Register in_right as freespec.core.eplus.in_right.

Infix "+" := eplus : eff_scope.

(** For [eplus] to be used seamlessly as a concrete eff composite, we
    provide the necessary instances for the [MayProvide], [Provide] and
    [Distinguish] type classes. Note that these instances always prefer the
    left operand of [eplus]. For instance, considering a situation where
    there is an instance for [F -< Fx] and an instance for [F -< Ex],
    the instance of [F -< (Fx + Ex)] will rely on [Fx].

    The main use case for [eplus] is to locally provide an additional
    eff. For instance, we can consider a [with_state] function which would
    locally give access to the [STORE] eff, that is [with_state : forall
    Fx s α, s -> freer (Fx + STORE s) α -> freer Fx α]. In such a case, the
    eff made locally available shall be the right operand of [eplus]. This
    way, functions such as [with_state] are reentrant. If we take an example,
    the following impure computation:

<<
with_state true (with_state false get)
>>

    will return false (that is, the variable in the inner store). *)

Instance refl_MayProvide (F : eff) : F -<? F :=
  { prj := fun _ e => Some e
  }.

Program Instance refl_Provide (F : eff) : F -< F :=
  { inj := fun (a : Type) (e : F a) => e
  }.

Instance eplus_left_MayProvide (Fx F E : eff) `{F -<? Fx}
  : F -<? (Fx + E) :=
  { prj := fun A e => if e is in_left e then prj e else None
                (* match e with *)
                (* | in_left e => prj e *)
                (* | _ => None *)
                (* end *)
  }.

Program Instance eplus_left_Provide (Fx F E : eff) `{F -< Fx}
  : F -< (Fx + E) :=
  { inj := fun (a : Type) (e : F a) => in_left (inj e)
  }.

Next Obligation. by rewrite injK_Some. Qed.

Instance eplus_right_MayProvide (F Ex E : eff) `{E -<? Ex}
  : E -<? (F + Ex) :=
  { prj := fun _ e =>
                match e with
                | in_right e => prj e
                | _ => None
                end
  }.

Program Instance eplus_right_Provide (F Ex E : eff) `{E -< Ex}
  : E -< (F + Ex) :=
  { inj := fun _ e => in_right (inj e)
  }.

Next Obligation. by rewrite injK_Some. Qed.

(** By default, Coq's inference algorithm for type classe instances inference is
    a depth-first search. This is not without consequence in our case. For
    instance, if we consider the search of an instance for [E -<? (F + E)],
    Coq will first try [eplus_right_MayProvide] (as explained previously),
    meaning he now searches for [E -<? F]. It turns out such an instance
    exists: [default_MayProvide].

    To circumvent this issue, we write a dedicated tactic [find_may_provide]
    which attempts to find an instance for [?F -<? (?Fx + ?Ex)] with
    [refl_MayProvide], [eplus_left_MayProvide] and [eplus_right_MayProvide]. *)

Ltac find_may_provide :=
  eapply refl_MayProvide +
  (eapply eplus_left_MayProvide; find_may_provide) +
  (eapply eplus_right_MayProvide; find_may_provide).

#[global] Hint Extern 1 (_ -<? (eplus _ _)) =>
  find_may_provide : typeclass_instances.

Program Instance refl_Distinguish (F E : eff)
  : @Distinguish F F E (refl_Provide F) (default_MayProvide F E).

Program Instance eplus_left_default_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Fx}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (default_MayProvide _ E).

Program Instance eplus_right_default_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Ex}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (default_MayProvide _ E).

Program Instance eplus_left_may_right_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Fx} `{M2 : E -<? Ex}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (eplus_right_MayProvide Fx Ex E).

Program Instance eplus_right_may_left_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Ex} `{M2 : E -<? Fx}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (eplus_left_MayProvide Fx E Ex).

Program Instance eplus_left_distinguish_left_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Fx} `{M2 : E -<? Fx}
   `{@Distinguish Fx F E P1 M2}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (eplus_left_MayProvide Fx E Ex).

Next Obligation.
  apply: injK_None.
Defined.

Program Instance eplus_right_distinguish_right_Distinguish (Fx Ex F E : eff)
   `{P1 : F -< Ex} `{M2 : E -<? Ex}
   `{@Distinguish Ex F E P1 M2}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (eplus_right_MayProvide Fx Ex E).

Next Obligation.
  apply: injK_None.
Defined.
