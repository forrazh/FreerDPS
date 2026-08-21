(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(******************************************************************************)
(* Definition of effects *)
(*                                                                            *)
(* effect := Type -> Type *)
(* MayProvide, -<? == TODO *)
(* prj == TODO *)
(* Provide, -< == TODO *)
(* inj == TODO (see Kiselyov) *)
(* Distinguish == *)
(*                                                                            *)
(* Examples of effect: *)
(* eempty == empty effect *)
(* STORE s == example of effect *)
(* FlipEff == effect for a probabilistic boolean choice *)
(*                                                                            *)
(* References: Kiselyov, FreeSpec *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun seq.
From monae Require Import hierarchy.

Local Open Scope monae_scope.

(** * Definition  *)

(** Following the definition of the <<operational>> package, effects in
    FreeSpec are parameterized inductive types whose terms purposely describe
    the primitives the effect provides. *)

Definition effect := Type -> Type.

Declare Scope effect_scope.
Bind Scope effect_scope with effect.

(** Given [F : effect], a term of type [F α] identifies a primitive of [F]
    expected to produce a result of type [α]. *)

(** * Polymorphic Effect Composites *)
Class MayProvide (Fx F : effect) : Type :=
  { prj: Fx ~~> option \o F}.
Arguments prj {_ _ _ _} _.

Notation "F -<? Fx" := (MayProvide Fx F)
  (at level 92, left associativity) : type_scope.

Class Provide (Fx F : effect) : Type :=
  { may_prov :: F -<? Fx ;
    inj : F ~~> Fx ;
    injK_Some {A} : forall e : F A, may_prov.(prj) (inj _ e) = Some e }.
Arguments inj {_ _ _ _} _.

Notation "F -< Fx" := (Provide Fx F)
  (at level 92, left associativity) : type_scope.

(** We provide a default instance for [MayProvide] in the form of a function
    [proj] which always return [None].  We give to this default instance a
    ridiculously high priority number to ensure it is selected only if no other
    instances are found. *)

Instance default_MayProvide (F E : effect) : (E -<? F) |1000 :=
  { prj := fun _ _ => None }.

(** It is expected that, for an effect composite [Fx] which provides [F] and
    may provide [E], [inj] and [proj] do not mix up [F] and [E]
    primitives. That is, injecting a primitive [e] of [F] inside [Fx], then
    projecting the resulting primitive into [E] returns [None] as long as [F]
    and [E] are two different effects. *)

Class Distinguish (Fx F E : effect) `{Hp: F -< Fx, Hmp : E -<? Fx} : Prop :=
  { injK_None : forall {A} (e: F A), Hmp.(prj) (Hp.(inj) e) = None }.

(** [EMember F Fs] records a position occupied by [F] in [Fs]. *)
(* Not using the mathcomp version to avoid relying on a too strict eqType *)
(* Based on ExtLib's Data/Member.v *)
Inductive EMember (F: effect) : seq effect -> Type :=
| EM0 Fs : EMember F (F :: Fs)
| EMNext G Fs :
    EMember F Fs -> EMember F (G :: Fs).

Arguments EM0 {F Fs}.
Arguments EMNext {F G Fs} EMemberF.
Existing Class EMember.
#[global] Existing Instance EM0.

#[global] Instance effect_EMember_next_instance
    (F G : effect) (Fs : seq effect) `{EMember F Fs} :
    EMember F (G :: Fs) | 10 :=
  EMNext H.

(** [HEMember EMemberF EMemberG] records that [EMemberF] identifies a
    position strictly before the position identified by [EMemberG]. *)
(* Based on Chlipala's heterogenous lists  *)
Inductive HEMember :
    forall F G Fs, EMember F Fs -> EMember G Fs -> Type :=
| EMB0 F G Fs (EMemberG : EMember G Fs) :
    HEMember F G (F :: Fs) EM0
      (EMNext EMemberG)
| EMBNext F G E Fs
    (EMemberF : EMember F Fs) (EMemberG : EMember G Fs) :
    HEMember F G Fs EMemberF EMemberG ->
    HEMember F G (E :: Fs) (EMNext EMemberF)
      (EMNext EMemberG).

Arguments EMB0 {F G Fs} EMemberG.
Arguments EMBNext {F G E Fs EMemberF EMemberG} beforeFG.
Existing Class HEMember.
#[global] Existing Instance EMB0.
#[global] Existing Instance EMBNext.

(** [StrictProvide Fx Fs] provides every effect in [Fs] and, for every pair
    of positions, distinguishes the effects in both directions.  Both
    properties use the same [Provide] witnesses. *)
Class StrictProvide (Fx : effect) (Fs : seq effect) : Type :=
  { strict_EMember_provide :
      forall F, EMember F Fs -> F -< Fx;
    strict_EMembers_distinguish :
      forall F G (EMemberF : EMember F Fs)
        (EMemberG : EMember G Fs),
        HEMember F G Fs EMemberF EMemberG ->
        @Distinguish Fx F G
            (strict_EMember_provide F EMemberF)
            (@may_prov Fx G (strict_EMember_provide G EMemberG)) /\
          @Distinguish Fx G F
            (strict_EMember_provide G EMemberG)
            (@may_prov Fx F (strict_EMember_provide F EMemberF)) }.

Arguments strict_EMember_provide {Fx Fs} StrictProvide F EMemberF.
Arguments strict_EMembers_distinguish {Fx Fs}
  StrictProvide F G EMemberF EMemberG beforeFG.

#[global] Instance strict_EMember_provide_instance
    (Fx F : effect) (Fs : seq effect)
    `{strictFs : StrictProvide Fx Fs}
    `{EMemberF : EMember F Fs} : F -< Fx | 100 :=
  strict_EMember_provide strictFs F EMemberF.

#[global] Instance strict_EMembers_distinguish_before_instance
    (Fx F G : effect) (Fs : seq effect)
    `{strictFs : StrictProvide Fx Fs}
    `{EMemberF : EMember F Fs}
    `{EMemberG : EMember G Fs}
    `{beforeFG : @HEMember F G Fs EMemberF EMemberG} :
    @Distinguish Fx F G
      (strict_EMember_provide strictFs F EMemberF)
      (@may_prov Fx G
        (strict_EMember_provide strictFs G EMemberG)) | 100 :=
  proj1 (strict_EMembers_distinguish strictFs F G
    EMemberF EMemberG beforeFG).

#[global] Instance strict_EMembers_distinguish_after_instance
    (Fx F G : effect) (Fs : seq effect)
    `{strictFs : StrictProvide Fx Fs}
    `{EMemberF : EMember F Fs}
    `{EMemberG : EMember G Fs}
    `{beforeGF : @HEMember G F Fs EMemberG EMemberF} :
    @Distinguish Fx F G
      (strict_EMember_provide strictFs F EMemberF)
      (@may_prov Fx G
        (strict_EMember_provide strictFs G EMemberG)) | 100 :=
  proj2 (strict_EMembers_distinguish strictFs G F
    EMemberG EMemberF beforeGF).

Notation "Fs -<< Fx" := (StrictProvide Fx Fs)
  (at level 50, no associativity) : type_scope.

#[global] Hint Mode MayProvide + + : typeclass_instances.
#[global] Hint Mode Provide + + : typeclass_instances.
#[global] Hint Mode Distinguish + + + - - :
  typeclass_instances.
#[global] Hint Mode EMember + + : typeclass_instances.
#[global] Hint Mode HEMember + + + + + : typeclass_instances.
#[global] Hint Mode StrictProvide + - : typeclass_instances.

(** * Composing Effects *)

(** We provide the [eplus] operator to compose effects together. That is,
    [eplus] can be used to build _concrete_ (as opposed to polymorphic)
    effect composite. *)

Inductive eplus (F E : effect) (α : Type) :=
| in_left (e : F α) : eplus F E α
| in_right (e : E α) : eplus F E α.

Arguments in_left [F E α] (e).
Arguments in_right [F E α] (e).

Register eplus as freespec.core.eplus.type.
Register in_left as freespec.core.eplus.in_left.
Register in_right as freespec.core.eplus.in_right.

Infix "+" := eplus : effect_scope.

(** For [eplus] to be used seamlessly as a concrete effect composite, we
    provide the necessary instances for the [MayProvide], [Provide] and
    [Distinguish] type classes. Note that these instances always prefer the
    left operand of [eplus]. For instance, considering a situation w0
    t0 is an instance for [F -< Fx] and an instance for [F -< Ex],
    the instance of [F -< (Fx + Ex)] will rely on [Fx].

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

Instance refl_MayProvide (F : effect) : F -<? F :=
  { prj := fun _ e => Some e }.

Program Instance refl_Provide (F : effect) : F -< F :=
  { inj := fun (a : Type) (e : F a) => e }.
Next Obligation. by move=> */=. Qed.

Instance eplus_left_MayProvide (Fx F E : effect) `{F -<? Fx}
  : F -<? (Fx + E) :=
  { prj := fun A e => if e is in_left e then prj e else None
                (* match e with *)
                (* | in_left e => proj e *)
                (* | _ => None *)
                (* end *)
  }.

Program Instance eplus_left_Provide (Fx F E : effect) `{F -< Fx}
  : F -< (Fx + E) :=
  { inj := fun (a : Type) (e : F a) => in_left (inj e)
  }.
Next Obligation. by move=> */=; rewrite injK_Some. Qed.

Instance eplus_right_MayProvide (F Ex E : effect) `{E -<? Ex}
  : E -<? (F + Ex) :=
  { prj := fun _ e => if e is in_right e then prj e else None }.

Program Instance eplus_right_Provide (F Ex E : effect) `{E -< Ex}
  : E -< (F + Ex) :=
  { inj := fun _ e => in_right (inj e) }.
Next Obligation. by move=> */=; rewrite injK_Some. Qed.

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

Program Instance refl_Distinguish (F E : effect)
  : @Distinguish F F E (refl_Provide F) (default_MayProvide F E).

Program Instance eplus_left_default_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Fx}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (default_MayProvide _ E).

Program Instance eplus_right_default_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Ex}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (default_MayProvide _ E).

Program Instance eplus_left_may_right_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Fx} `{M2 : E -<? Ex}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (eplus_right_MayProvide Fx Ex E).

Program Instance eplus_right_may_left_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Ex} `{M2 : E -<? Fx}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (eplus_left_MayProvide Fx E Ex).

Program Instance eplus_left_distinguish_left_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Fx} `{M2 : E -<? Fx}
   `{@Distinguish Fx F E P1 M2}
  : @Distinguish (Fx + Ex) F E
                 (eplus_left_Provide Fx F Ex)
                 (eplus_left_MayProvide Fx E Ex).
Next Obligation. by move=> */=. Qed.
Next Obligation. by move=> */=; exact: injK_None. Defined.
Next Obligation. by move=> */=. Defined.

Program Instance eplus_right_distinguish_right_Distinguish (Fx Ex F E : effect)
   `{P1 : F -< Ex} `{M2 : E -<? Ex}
   `{@Distinguish Ex F E P1 M2}
  : @Distinguish (Fx + Ex) F E
                 (eplus_right_Provide Fx Ex F)
                 (eplus_right_MayProvide Fx Ex E).
Next Obligation. by move=> */=. Qed.
Next Obligation. by move=> */=; exact: injK_None. Defined.
Next Obligation. by move=> */=. Qed.
Next Obligation. by move=> */=. Qed.

Inductive eempty : effect := .

(** Another example of general-purpose effect we can define is the [STORE s]
    effect, w0 [s] is a type for a state, and [STORE s] allows for
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
    parameterized by [F ⊕ E] can t0fore leverage the primitives of both [F]
    and [E]. *)

