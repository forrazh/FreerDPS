(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import Init.
(* WARNING: Move this import to its MathComp counterpart. *)
From Stdlib Require Import Arith.
From mathcomp Require Import all_boot classical_sets.
From FreerDPS Require Import Core Freer Hoare.

Import FreerFuns.
Generalizable All Variables.


(** * Specifying *)
(* Opaque denote. *)


Module Export DoorsControllerM.
(** ** Doors *)

Inductive door : Type := left | right.

HB.instance Definition _ := gen_eqMixin door.

Inductive DOORS : effect :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Section doors_s.
Context `{Provide Fx DOORS} {im : freerMonad Fx}.

Definition is_open (d : door) : im bool := trigger $ IsOpen d.
Definition toggle (d : door) : im unit := trigger $ Toggle d.
Definition open_door (d : door) : im unit :=
  is_open d >>= fun open => when (~~ open) (toggle d).
Definition close_door (d : door) : im unit :=
  is_open d >>= (when ^~ (toggle d)).
End doors_s.
(** ** Controller *)

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Section controller_s.
Context `{Provide Fx CONTROLLER} {im : freerMonad Fx}.
Definition tick : im unit := trigger Tick.
Definition request_open (d : door) : im unit := trigger $ RequestOpen d.
End controller_s.

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller `{Provide Fx DOORS, Provide Fx (STORE nat)}
    {im : freerMonad Fx} : component (im:=im) CONTROLLER Fx :=
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
Inductive doors_o_caller : Ω -> forall (a : Type), DOORS a -> Prop :=
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

(* doors_c => {{door_caller}} p%step {{door_callee}} *)
Definition doors_c : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.
(* -------------------------------------------------------------------------- *)

Section doors_pre_post_helpers.
Context `{Provide Fx DOORS} {a : Type}.

Lemma doors_effect_preE (op : Fx a) (ω : Ω) :
  pre (hoare_of_contract doors_c op) ω <->
  match proj_p op with
  | Some door_op => doors_o_caller ω a door_op
  | None => True
  end.
Proof. by rewrite /hoare_of_contract /= /gen_caller_obligation. Qed.

Lemma doors_effect_postE
    (op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  post (hoare_of_contract doors_c op) ω x ω' <->
  match proj_p op with
  | Some door_op =>
      ω' = step ω a door_op x /\ doors_o_callee ω a door_op x
  | None => ω' = ω
  end.
Proof.
rewrite /hoare_of_contract /= /gen_witness_update
  /gen_callee_obligation.
case: (proj_p op)=> [door_op |] /=.
- by [].
by split=> [[-> _] | ->].
Qed.

Lemma doors_pre_condE
    (ω : Ω) (op : DOORS a) :
  pre (hoare_of_contract doors_c (inj_p op)) ω <->
  doors_o_caller ω a op.
Proof. by rewrite doors_effect_preE proj_inj_p_equ. Qed.

Lemma doors_post_condE
    (ω : Ω) (op : DOORS a) (x : a) (ω' : Ω) :
  post (hoare_of_contract doors_c (inj_p op)) ω x ω' <->
  ω' = step ω a op x /\ doors_o_callee ω a op x.
Proof. by rewrite doors_effect_postE proj_inj_p_equ. Qed.
End doors_pre_post_helpers.

Opaque hoare_of_contract.

(*--------------------------- Intermediary Lemmas ----------------------------*)
Section IntermLemmaS.
Context `{Provide Fx DOORS} (ω : Ω) (d : door).

Lemma doors_is_open_post_retE (opened : bool) (ω' : Ω) :
  post (hoare_of_contract doors_c
          (A := bool) (inj_p (IsOpen d))) ω opened ω' <->
  post (@ret (hoare Ω) bool (sel d ω)) ω opened ω'.
Proof.
rewrite doors_post_condE hoare_pureE;
  split=> [ [-> callee] | [<- <-] ];
  split=> //.
- by inversion callee; ssubst.
- exact: doors_o_callee_is_open.
Qed.

Lemma doors_is_open_preE :
  pre (hoare_of_contract doors_c
          (A := bool) (inj_p (IsOpen d))) ω <->
  pre (@ret (hoare Ω) bool (sel d ω)) ω.
Proof.
by rewrite hoare_pureE; split=> // _;
  rewrite doors_pre_condE;
  exact: req_is_open.
Qed.

Lemma doors_toggle_postE (u : unit) (ω' : Ω) :
  post (hoare_of_contract doors_c
          (A := unit) (inj_p (Toggle d))) ω u ω' <->
  ω' = tog d ω.
Proof.
by rewrite doors_post_condE;
  split=> [ [-> _] | ->] //; split=>//;
  exact: doors_o_callee_toggle.
Qed.

Lemma doors_toggle_preE
    (* Safe means : door 1 is closed -> door 2 is closed *)
    (* Previous: (safe : sel d ω = false -> sel (co d) ω = false) *)
    (safe : sel (co d) ω -> sel d ω) :
  pre (hoare_of_contract doors_c
          (A := unit) (inj_p (Toggle d))) ω <->
  pre (@ret (hoare Ω) unit tt) ω.
Proof.
by rewrite hoare_pureE; split=> // _;
  rewrite doors_pre_condE;
  exact: req_toggle safe.
Qed.
End IntermLemmaS.

Local Open Scope classical_set_scope.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : ~~sel d ω \/ ~~sel (co d) ω)
  : forall (d' : door), ~~sel d' ω \/ ~~sel (co d') ω.
Proof.
by move: d safe=> + /[swap]; case; case=>//=; rewrite or_comm.
Qed.

Definition doors_safe (ω : Ω) := ~~ sel left ω \/ ~~ sel right ω.

Section RespectfulAndRunLemmas.
Context `{Provide Fx DOORS} {im : freerMonad Fx}.
Local Notation "p ||= c" := (to_hoare (im:=im) c p) (at level 70).

(** Closing a door [d] in any system [ω] is always a respectful operation. *)
Lemma close_door_respectful (d : door) :
  pre (close_door d ||= doors_c) = [set: _].
Proof.
rewrite /close_door -subTset=> ω _; apply: th_pre_bindA.
- by rewrite to_hoare_requestE doors_is_open_preE.
case=> ?;
  rewrite to_hoare_when_preE // to_hoare_requestE doors_is_open_post_retE
  => -[? <-].
by rewrite to_hoare_requestE;
  apply/(doors_toggle_preE ω d).
Qed.

Lemma open_door_respectful (ω : Ω) (d : door) (safe : ~~ sel (co d) ω) :
  pre (open_door d ||= doors_c) ω.
Proof.
rewrite /open_door; apply: th_pre_bindA.
- by rewrite to_hoare_requestE doors_is_open_preE.
case=> ?;
  rewrite to_hoare_when_preE // to_hoare_requestE doors_is_open_post_retE
  => -[_ <-].
rewrite to_hoare_requestE;
  apply/(doors_toggle_preE ω d)=>//.
by move: safe=> /[swap] ->.
Qed.

Lemma close_door_run (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (close_door d ||= doors_c) ω x ω') :
~~ sel d ω'.
Proof.
move: run; rewrite /close_door th_post_bindA.
move=> [opened [? [ ]]].
rewrite to_hoare_requestE doors_is_open_post_retE to_hoare_when_postE
  => -[+ <-].
case: opened=> [ + [[]] | /[swap] -> -> ] //.
by rewrite to_hoare_requestE doors_toggle_postE
  => /[swap] ->;
  rewrite tog_equ_1=> ->.
Qed.

Opaque close_door.
Opaque open_door.
Opaque Nat.ltb.
Opaque sel.

Lemma doors_request_preserves_safe
    `(op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  pre (trigger op ||= doors_c) ω ->
  post (trigger op ||= doors_c) ω x ω' ->
  doors_safe ω -> doors_safe ω'.
Proof.
rewrite to_hoare_requestE doors_effect_preE doors_effect_postE.
case: (proj_p op)=> [door_op |] /=; last first.
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

Lemma doors_handler_preserves_safe `(op : Fx a) :
  preserves_invariant doors_safe (hoare_of_contract doors_c op).
Proof.
by move=> state result state' op_pre op_post state_safe;
  apply: (doors_request_preserves_safe op state result state');
  rewrite ?to_hoare_requestE.
Qed.

(** /!\ WARNING: This proof exits the Equational Reasoning.
  * This is a known issue. I need to find a way to remove this
  * induction but can't find one right now.
  *)
Lemma doors_run_preserves_safe `(p : freer Fx A) :
  preserves_invariant doors_safe (p |= doors_c).
Proof.
elim: p=> [value | X op k IH].
- exact: preserves_invariant_ret.
exact: (preserves_invariant_bind (doors_handler_preserves_safe op) IH).
Qed.

Lemma respectful_run_inv `(p : im A)
    (ω : Ω) (safe : ~~ sel left ω \/ ~~ sel right ω)
    (a : A) (ω' : Ω)
    (hpre : pre (p |= doors_c) ω)
    (hpost : post (p |= doors_c) ω a ω') :
  ~~ sel left ω' \/ ~~ sel right ω'.
Proof.
by move: hpre hpost safe;
  rewrite -ToHoareFreerBridge.to_hoare_reifyE;
  exact: doors_run_preserves_safe.
Qed.
End RespectfulAndRunLemmas.

(** ** Main Theorem *)
Section controller_s.
Context `{StrictProvide2 Fx DOORS (STORE nat)} {im : freerMonad Fx}.

Lemma controller_pre `(op: CONTROLLER α) (ω : Ω)
  : pre ((controller (im:=im) α op) |= doors_c) ω.
Proof.
case: op=> [|d].
- apply: th_pre_bindA.
  + exact: to_hoare_distinguished_request_preI.
  + move=> cpt? /to_hoare_distinguished_request_postE ->.
    rewrite to_hoare_when_preE;
      case: (15 <? cpt)%nat=> //=;
      apply: th_pre_bindA.
    * by apply: th_pre_bindA=>[|*];
        rewrite close_door_respectful.
    * by move=>*;
        exact: to_hoare_distinguished_request_preI.

- apply: th_pre_bindA=>[|*].
  + apply: th_pre_bindA.
    * by rewrite close_door_respectful.
    * by move=>?? Hclose; exact/open_door_respectful/close_door_run/Hclose.
  + exact: to_hoare_distinguished_request_preI.
Qed.

Theorem controller_correct
  : correct_component controller (im:=im)
    (no_contract CONTROLLER) doors_c (fun=> doors_safe).
Proof.
move=>? ω ?? op _.
split=> [|?? postc]; [exact: controller_pre|split=> //].
have prec := controller_pre op ω; move: prec postc.
exact: respectful_run_inv.
Qed.

End controller_s.
