(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import all_boot classical_sets boolp.
From monae Require Import hierarchy.
(* WARNING: Move this import to its MathComp counterpart. *)
From Stdlib Require Import Arith.
From FreerDPS Require Import Core.

Import FreerFuns.

Module Export DoorsControllerM.
(** ** Doors *)

Inductive door : Type := left | right.

HB.instance Definition _ := gen_eqMixin door.

Inductive DOORS : effect :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Section doors_s.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.

Definition is_open (d : door) : M bool := trigger $ IsOpen d.
Definition toggle (d : door) : M unit := trigger $ Toggle d.
Definition open_door (d : door) : M unit :=
  is_open d >>= fun open => when (~~ open) (toggle d).
Definition close_door (d : door) : M unit :=
  is_open d >>= (when ^~ (toggle d)).
End doors_s.

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Section controller_s.
Context {Fx : effect} `{CONTROLLER -< Fx} {M : freerMonad Fx}.
Definition tick : M unit := trigger Tick.
Definition request_open (d : door) : M unit := trigger $ RequestOpen d.
End controller_s.

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller {Fx : effect} `{DOORS -< Fx, (STORE nat) -< Fx}
    {M : freerMonad Fx} : component (M:=M) CONTROLLER Fx :=
  fun _ op =>
    match op with
    | Tick =>
      iget >>= fun cpt =>
      when (15 <? cpt)%nat $
        close_door left >>
        close_door right >>
        iput 0%nat
    | RequestOpen d =>
      close_door (co d) >>
      open_door d >>
      iput 0%nat
    end.
End DoorsControllerM.

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(* ----------------------------- Witness States ----------------------------- *)

Definition Ω : Type := bool * bool.
(*         S : Type := left * rght. *)

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (~~ (fst ω), snd ω)
  | right => (fst ω, ~~ (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = ~~ (sel d ω).
Proof. by case: d. Qed.

Lemma tog_equ_2 (d : door) (ω : Ω)
  : sel (co d) (tog d ω) = sel (co d) ω.
Proof. by case: d. Qed.

Opaque tog.

(* -------------------------------------------------------------------------- *)

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

(* -------------------------------- Contract -------------------------------- *)
(* Ω = bool * bool : doors state *)
Definition step (ω : Ω) (a : Type) (op : DOORS a) (_ : a) : Ω :=
  if op is Toggle d then tog d ω else ω.

(** *** Requirements / Precondition *)
Inductive doors_o_caller : Ω -> forall (a : Type), set $ DOORS a :=
(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)
| req_is_open (d : door) (ω : Ω)
  : doors_o_caller ω bool (IsOpen d)
(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed too for a request to toggle [d] to be valid. *)
| req_toggle (d : door) (ω : Ω) (H : sel (co d) ω -> sel d ω)
  : doors_o_caller ω unit (Toggle d).

(** *** Promises / PostCondition *)
Inductive doors_o_callee : Ω -> forall (a : Type), DOORS a -> a -> Prop :=
(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)
| doors_o_callee_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : doors_o_callee ω bool (IsOpen d) x
(** - There is no particular requirement on the result [x] of a request for
      [ω] to close the door [d]. *)
| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

Lemma doors_o_callee_is_openE
    {ω : Ω} {d : door} {opened : bool} :
  doors_o_callee ω bool (IsOpen d) opened ->
  sel d ω = opened.
Proof. by inversion 1;ssubst. Qed.

(* doors_c => {{door_caller}} p%step {{door_callee}} *)
Definition doors_c : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.
(* -------------------------------------------------------------------------- *)

Local Open Scope classical_set_scope.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : ~~sel d ω \/ ~~sel (co d) ω)
  : forall (d' : door), ~~sel d' ω \/ ~~sel (co d') ω.
Proof.
by move: d safe=> + /[swap]; case; case=>//=; rewrite or_comm.
Qed.

Definition doors_safe (ω : Ω) := ~~ sel left ω \/ ~~ sel right ω.

Section RespectfulAndRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" :=
  (to_hoare (M:=M) c p)
  (at level 50, no associativity).

(** Closing a door [d] in any system [ω] is always a respectful operation. *)
Lemma close_door_respectful (d : door) :
  pre (doors_c ||> close_door d) = [set: _].
Proof.
rewrite /close_door -subTset=> hω _; apply: th_pre_bindA.
- by rewrite to_hoare_trigger_preE; exact: req_is_open.
case=> ?;
  rewrite to_hoare_when_preE // to_hoare_trigger_postE
    => -[ /[swap] ]=>/doors_o_callee_is_openE ? -> .
by rewrite to_hoare_trigger_preE;
  apply: req_toggle.
Qed.

Lemma open_door_respectful (ω : Ω) (d : door) (safe : ~~ sel (co d) ω) :
  pre (doors_c ||> open_door d) ω.
Proof.
rewrite /open_door; apply: th_pre_bindA.
- by rewrite to_hoare_trigger_preE; exact: req_is_open.
case=> ?;
  rewrite to_hoare_when_preE // to_hoare_trigger_postE
    => -[ /[swap] ]=>/doors_o_callee_is_openE ? ->.
rewrite /= to_hoare_trigger_preE;
  apply: req_toggle=>//.
by move: safe=> /[swap] ->.
Qed.

Lemma close_door_run (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (doors_c ||> close_door d) ω x ω') :
~~ sel d ω'.
Proof.
move: run; rewrite /close_door th_post_bindA;
  move=> [opened [? [ ] ] ];
  rewrite to_hoare_trigger_postE /=;
  rewrite to_hoare_when_postE=> -[<-] //;
  case: opened=> /doors_o_callee_is_openE=> [H' [?] | /[swap] <- ->] //.
by rewrite to_hoare_trigger_postE /= => -[-> _];
  rewrite tog_equ_1 H'.
Qed.

Opaque close_door.
Opaque open_door.
Opaque Nat.ltb.
Opaque sel.

Lemma doors_request_preserves_safe
    {a : Type} (op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  pre (doors_c ||> trigger op) ω ->
  post (doors_c ||> trigger op) ω x ω' ->
  doors_safe ω -> doors_safe ω'.
Proof.
rewrite to_hoare_request_preE to_hoare_request_postE.
case: (proj op)=> [door_op |] /=; last first.
- by move=> _ ->.
move=> + [-> _].
move: door_op x; case=> d [] caller safe //=.
apply: (one_door_safe_all_doors_safe _ d).
move: safe=> /one_door_safe_all_doors_safe /(_ d).
case=> [d_closed | ?]; right; rewrite tog_equ_2 //.
apply/negP=> co_open; move/negP: d_closed=> d_closed.
by inversion caller as [|?? Hsafe]; subst;
  move: co_open Hsafe d_closed=> -> ->.
Qed.

Lemma doors_handler_preserves_safe {a : Type} (op : Fx a) :
  preserves_invariant doors_safe (hoare_of_contract doors_c op).
Proof.
move=> ??? Hpre Hpost.
apply: doors_request_preserves_safe;
  rewrite to_hoare_requestE.
- exact: Hpre.
- exact: Hpost.
Qed.
End RespectfulAndRunLemmas.

(* From now on, proofs will use the inductive version. *)
Section InvariantRunLemmas.
Context {Fx : effect} `{DOORS -< Fx} {M : inductiveFreerMonad Fx}.

(** /!\ WARNING: This lemma is the only one needing `f_ind`  because we
  * require to "execute" the freer program in order to denote it and see
  * if the invariant was preserved all along.
  *)
Lemma doors_run_preserves_safe {A : Type} (p : M A) :
  preserves_invariant doors_safe (doors_c |> p).
Proof.
by apply: to_hoare_preserves_invariant=> *;
  exact: (doors_handler_preserves_safe (M:=M)).
Qed.

Lemma respectful_run_inv {A : Type} (p : M A)
    (ω : Ω) (safe : doors_safe ω)
    (a : A) (ω' : Ω)
    (hpre : pre (doors_c |> p) ω)
    (hpost : post (doors_c |> p) ω a ω') :
  doors_safe ω'.
Proof. by move: hpre hpost safe; exact: doors_run_preserves_safe. Qed.
End InvariantRunLemmas.

(** ** Main Theorem *)
Section controller_s.
Context {Fx : effect} `{StrictProvide2 Fx DOORS (STORE nat)}
  {M : inductiveFreerMonad Fx}.

Lemma controller_pre {α : Type} (op : CONTROLLER α) (ω : Ω)
  : pre (doors_c |> controller (M:=M) α op) ω.
Proof.
case: op=> [|d].
- (* Tick *) apply: th_pre_bindA.
  + exact: to_hoare_distinguished_request_preI.
  + move=> cpt? /to_hoare_distinguished_request_postE ->.
    rewrite to_hoare_when_preE;
      case: (15 <? cpt)%nat=> //=;
      apply: th_pre_bindA.
    * by apply: th_pre_bindA=>[|*];
        rewrite close_door_respectful.
    * by move=>*;
        exact: to_hoare_distinguished_request_preI.
- (* Request Open *) apply: th_pre_bindA=>[|*].
  + apply: th_pre_bindA.
    * by rewrite close_door_respectful.
    * by move=>?? Hclose; exact/open_door_respectful/close_door_run/Hclose.
  + exact: to_hoare_distinguished_request_preI.
Qed.

Theorem controller_correct
  : correct_component controller (M:=M)
    (no_contract CONTROLLER) doors_c (fun=> doors_safe).
Proof.
move=>? ω ?? op _; split=> [|?? Hpost]; [exact: controller_pre|split=> //].
have Hpre := controller_pre op ω; move: Hpre Hpost.
exact: respectful_run_inv.
Qed.

End controller_s.
