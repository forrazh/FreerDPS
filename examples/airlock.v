(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import Init.
(* WARNING: Move this import to its MathComp counterpart. *)
From Stdlib Require Import Arith.
From mathcomp Require Import all_boot classical_sets.
From FreerDPS Require Import Core Freer Hoare HoareFacts.
From examples Require Import airlock_helper.

Import SpecializedHoareModule.

Create HintDb airlock.

(** * Specifying *)

(** ** Doors *)

Inductive door : Type := left | right.

HB.instance Definition _ := gen_eqMixin door.

Inductive DOORS : effect :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Generalizable All Variables.

Section airlock_s.

Import FreerFuns.

Definition is_open `{Provide Fx DOORS} {im : freerMonad Fx} (d : door) :
    im bool :=
  trigger (inj_p $ IsOpen d).

Definition toggle `{Provide Fx DOORS} {im : freerMonad Fx} (d : door) :
    im unit :=
  trigger (inj_p $ Toggle d).

Definition open_door `{Provide Fx DOORS} {im : freerMonad Fx}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when (~~ open) (toggle d).

Definition close_door `{Provide Fx DOORS} {im : freerMonad Fx}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide Fx CONTROLLER} {im : freerMonad Fx} : im unit :=
  trigger (inj_p Tick).

Definition request_open `{Provide Fx CONTROLLER} {im : freerMonad Fx}
    (d : door) : im unit :=
  trigger (inj_p $ RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller `{Provide Fx DOORS, Provide Fx (STORE nat)}
    {im : freerMonad Fx} : component (im:=im) CONTROLLER Fx
  (* .
  move=> X; case=> [|d].
  - apply/bind=>[|cpt].
    + apply/iget.
    + apply/when.
      * apply: (15 <? cpt).
      * apply/bind=>[|_].
      -- apply/close_door/left.
      -- apply/bind=>[|_].
        ++ apply/close_door/right.
        ++ apply/iput/0.
  - apply/bind=>[|_].
    + apply/close_door/co/d.
    + apply/bind=>[|_].
      * apply/open_door/d.
      * apply/iput/0.
  Show Proof. *)
   :=
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

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(** *** Witness States *)

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

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

#[local] Opaque tog.
Opaque denote.

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
  (* H : ~~ sel (co d) ω *)

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

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.
(* => {{door_caller}} p%step {{door_callee}} *)

Lemma doors_effect_preE {Fx a} `{MayProvide Fx DOORS}
    (op : Fx a) (ω : Ω) :
  pre (hoare_of_contract doors_contract op) ω <->
  match proj_p op with
  | Some door_op => doors_o_caller ω a door_op
  | None => True
  end.
Proof. by rewrite /hoare_of_contract /= /gen_caller_obligation. Qed.

Lemma doors_o_caller_preE `{Provide Fx DOORS} {a}
    (ω : Ω) (op : DOORS a) :
  pre (hoare_of_contract doors_contract (inj_p op)) ω <->
  doors_o_caller ω a op.
Proof. by rewrite doors_effect_preE proj_inj_p_equ. Qed.

Lemma doors_o_caller_preI `{Provide Fx DOORS} {a}
    (ω : Ω) (op : DOORS a) :
  doors_o_caller ω a op ->
  pre (hoare_of_contract doors_contract (inj_p op)) ω.
Proof. by rewrite doors_o_caller_preE. Qed.

Lemma doors_effect_postE {Fx a} `{MayProvide Fx DOORS}
    (op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  post (hoare_of_contract doors_contract op) ω x ω' <->
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

Lemma doors_o_callee_postE `{Provide Fx DOORS} {a}
    (ω : Ω) (op : DOORS a) (x : a) (ω' : Ω) :
  post (hoare_of_contract doors_contract (inj_p op)) ω x ω' <->
  ω' = step ω a op x /\ doors_o_callee ω a op x.
Proof. by rewrite doors_effect_postE proj_inj_p_equ. Qed.

Lemma doors_other_effect_postE {Fx a} `{MayProvide Fx DOORS}
    (op : Fx a) (other : proj_p op = None)
    (ω : Ω) (x : a) (ω' : Ω) :
  post (hoare_of_contract doors_contract op) ω x ω' <-> ω' = ω.
Proof.
by rewrite doors_effect_postE other.
Qed.

Opaque hoare_of_contract.

(** ** Intermediary Lemmas *)
Lemma doors_is_open_calleeE (ω : Ω) (d : door) (x : bool) :
  doors_o_callee ω bool (IsOpen d) x -> sel d ω = x.
Proof. by case: x=> postc; inversion postc; ssubst. Qed.

Lemma doors_is_open_effect_retE `{Provide Fx DOORS}
    (ω : Ω) (d : door) (opened : bool) (ω' : Ω) :
  post (hoare_of_contract doors_contract
          (A := bool) (inj_p (IsOpen d))) ω opened ω' <->
  post (@ret (hoare Ω) bool (sel d ω)) ω opened ω'.
Proof.
rewrite doors_o_callee_postE hoare_pure_postE /=.
split=> [ [-> callee] | [<- <-] ]; split=> //.
- exact: doors_is_open_calleeE callee.
- exact: doors_o_callee_is_open.
Qed.

Lemma doors_is_open_effect_ret_callerE `{Provide Fx DOORS}
    (ω : Ω) (d : door) :
  pre (hoare_of_contract doors_contract
          (A := bool) (inj_p (IsOpen d))) ω <->
  pre (@ret (hoare Ω) bool (sel d ω)) ω.
Proof.
by rewrite hoare_pure_preE; split=> // _;
  apply: doors_o_caller_preI; exact: req_is_open.
Qed.

Lemma doors_toggle_effect_postE `{Provide Fx DOORS}
  (ω : Ω) (d : door) (u : unit) (ω' : Ω) :
  post (hoare_of_contract doors_contract
          (A := unit) (inj_p (Toggle d))) ω u ω' <->
  ω' = tog d ω.
Proof.
by rewrite doors_o_callee_postE;
  split=> [ [-> _] | ->] //; split=>//;
  exact: doors_o_callee_toggle.
Qed.

Lemma doors_toggle_effect_ret_callerE `{Provide Fx DOORS}
    (ω : Ω) (d : door)
    (* Safe : porte 1 ferméE -> porte 2 ferméE *)
    (* (safe : sel d ω = false -> sel (co d) ω = false) *)
    (safe : sel (co d) ω -> sel d ω) :
  pre (hoare_of_contract doors_contract
          (A := unit) (inj_p (Toggle d))) ω <->
  pre (@ret (hoare Ω) unit tt) ω.
Proof.
by rewrite hoare_pure_preE; split=> // _;
  apply: doors_o_caller_preI; exact: req_toggle safe.
Qed.


Lemma doors_toggle_callerE (ω : Ω) (d : door) :
  doors_o_caller ω unit (Toggle d) ->
  sel (co d) ω -> sel d ω.
Proof. by move: ω d=> [[|] [|]] [|] //=; inversion 1. Qed.

(** Closing a door [d] in any system [ω] is always a respectful operation. *)
Local Open Scope classical_set_scope.


(* TODO(cleanup): Check whether this proof can be shortened. *)
Lemma close_door_respectful `{Provide Fx DOORS} {im : freerMonad Fx}
    (d : door) :
  pre (to_hoare (im:=im) doors_contract (close_door d)) = [set: _].
Proof.
rewrite /close_door -subTset=> ω _; apply: to_hoare_bind_preI.
- by rewrite to_hoare_requestE doors_is_open_effect_ret_callerE.
move=> [|] ω';
  rewrite to_hoare_when_preE // to_hoare_requestE doors_is_open_effect_retE
  => -[d_open <-].
by rewrite to_hoare_requestE;
  apply/(doors_toggle_effect_ret_callerE ω d).
Qed.

(* TODO(cleanup): Check whether this proof can be shortened. *)
Lemma open_door_respectful `{Provide Fx DOORS} {im : freerMonad Fx}
    (ω : Ω) (d : door) (safe : ~~ sel (co d) ω) :
  pre (to_hoare (im:=im) doors_contract
    (open_door (Fx := Fx) d)) ω.
Proof.
rewrite /open_door; apply: to_hoare_bind_preI.
- by rewrite to_hoare_requestE doors_is_open_effect_ret_callerE.
move=> [|] ω'; rewrite to_hoare_when_preE //
  to_hoare_requestE doors_is_open_effect_retE
  => -[_ <-].
rewrite to_hoare_requestE;
  apply/(doors_toggle_effect_ret_callerE ω d)=>//.
by move: safe=> /[swap] ->.
Qed.

Lemma close_door_run `{Provide Fx DOORS} {im : freerMonad Fx}
  (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (to_hoare (im:=im) doors_contract (close_door d)) ω x ω') :
~~ sel d ω'.
Proof.
move: run; rewrite /close_door to_hoare_bind_postE.
move=> [opened [? [ ]]].
rewrite to_hoare_requestE doors_is_open_effect_retE to_hoare_when_postE
  => -[+ <-].
case: opened.
- by move=> + [[] ];
  rewrite to_hoare_requestE doors_toggle_effect_postE=> /[swap] ->;
  rewrite tog_equ_1=> ->.
by move=> /[swap] -> ->.
Qed.

#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : ~~sel d ω \/ ~~sel (co d) ω)
  : forall (d' : door), ~~sel d' ω \/ ~~sel (co d') ω.
Proof.
by move: d safe=> + /[swap]; case; case=>//=; rewrite or_comm.
Qed.

(** The objective of this lemma is to prove that, if either the right door or
    the left door is closed, then after any respectful run of a computation
    [p] that interacts with doors, this fact remains true. *)

#[local] Opaque sel.
Definition doors_safe (ω : Ω) :=
  ~~ sel left ω \/ ~~ sel right ω.

(* TODO(cleanup): Check whether this proof can be shortened. *)
Lemma doors_request_preserves_safe `{Provide Fx DOORS}
    {im : freerMonad Fx}
    `(op : Fx a) (ω : Ω) (x : a) (ω' : Ω) :
  pre (to_hoare (im:=im) doors_contract (trigger op)) ω ->
  post (to_hoare (im:=im) doors_contract (trigger op)) ω x ω' ->
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

Lemma doors_handler_preserves_safe `{Provide Fx DOORS}
    {im : freerMonad Fx} {A} (op : Fx A) :
  preserves_invariant doors_safe
    (hoare_of_contract doors_contract op).
Proof.
by move=> state result state' op_pre op_post state_safe;
  apply: (doors_request_preserves_safe (im:=im) op state result state');
  rewrite ?to_hoare_requestE.
Qed.

Lemma doors_run_preserves_safe `{Provide Fx DOORS}
    {A} (p : freer Fx A) :
  preserves_invariant doors_safe
    (p |= doors_contract).
Proof.
elim: p=> [value | X op k IH].
- by rewrite to_hoare_localE; exact: preserves_invariant_ret.
exact: (preserves_invariant_bind
  (doors_handler_preserves_safe (im:=freer Fx) op) IH).
Qed.

Lemma respectful_run_inv `{Provide Fx DOORS} {A} (p : freer Fx A)
    (ω : Ω) (safe : ~~ sel left ω \/ ~~ sel right ω)
    (a : A) (ω' : Ω)
    (hpre : pre (to_hoare (im:=freer Fx) doors_contract p) ω)
    (hpost : post (to_hoare (im:=freer Fx) doors_contract p) ω a ω') :
  ~~ sel left ω' \/ ~~ sel right ω'.
(** The induction in [doors_run_preserves_safe] reduces this proof to showing
    that every handled request preserves [doors_safe]. It accounts for the
    following two cases:

    - Either [p] is a pure computation; in such a case, the doors state
      does not change, hence the proof is trivial.

    - Or [p] consists in a request to the doors effect, and a continuation
      whose domain satisfies the theorem, i.e. it preserves the invariant that
      either the left or the right door is closed.  Due to this hypothesis, we
      only have to prove that the first request made by [p] does not break the
      invariant. We consider two cases.

      - Either the computation asks for the state of a given door ([IsOpen]),
        then again the doors state does not change and the proof is trivial.
      - Or the computation wants to toggle a door [d].  We know by hypothesis
        that either [d] is closed or [d] is open (thanks to the
        [one_door_safe_all_doors_safe] result and the [safe] hypothesis).
        Again, we consider both cases.

         - If [d] is closed —and therefore will be opened—, then because we
           consider a respectful run, [co d] is necessarily closed too (it is a
           requirements of [door_contract]). Once [d] is opened, [co d] is still
           closed.
         - Otherwise, [co d] is closed, which means once [d] is toggled (no
           matter its initial state), then [co d] is still closed.

         That is, we prove that, when [p] toggles [d], [co d] is necessarily
         closed after the request has been handled.  Because there is at least
         one door closed ([co d]), we can conclude that either the right or the
         left door is closed thanks to [one_door_safe_all_doors_safe]. *)
Proof.
by move: hpre hpost safe; exact: doors_run_preserves_safe.
Qed.

(** ** Main Theorem *)
(* TODO(cleanup): Check whether this proof can be shortened. *)
Theorem controller_correct
    `{StrictProvide2 Fx DOORS (STORE nat)}
  : correct_component controller
    (im:=freer Fx)
    (no_contract CONTROLLER)
    doors_contract
    (fun _ ω => ~~ sel left ω \/ ~~ sel right ω).
Proof.
rewrite /correct_component=> ωF ω safe α op _.
have controller_pre :
    pre (to_hoare doors_contract
      (controller (im:=freer Fx) α op)) ω.
  case: op=> [|d]; rewrite /controller.
  - apply: to_hoare_bind_preI.
    + exact: to_hoare_distinguished_request_preI.
    move=> cpt state /to_hoare_distinguished_request_postE ->.
    rewrite to_hoare_when_preE.
    case: (15 <? cpt)%nat=> //=.
    apply: to_hoare_bind_preI.
    + by apply: to_hoare_bind_preI=>
        [|result state' close_post]; rewrite close_door_respectful.
    by move=> result state' closes_post;
      exact: to_hoare_distinguished_request_preI.
  apply: to_hoare_bind_preI.
  - apply: to_hoare_bind_preI.
    + by rewrite close_door_respectful.
    move=> result state close_post.
    exact: (open_door_respectful (Fx:=Fx) (im:=freer Fx) state d
      (close_door_run ω (co d) state result close_post)).
  by move=> result state body_post;
    exact: to_hoare_distinguished_request_preI.
split=> // x ω' run; split; first exact: mk_no_callee_obligation.
exact: (respectful_run_inv (Fx:=Fx)
  (controller (im:=freer Fx) α op) ω safe x ω' controller_pre run).
Qed.

End airlock_s.
