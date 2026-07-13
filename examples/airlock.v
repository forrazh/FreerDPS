(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From Stdlib Require Import Arith.
From FreerDPS Require Import Core Impure Hoare HoareFacts.
From monae Require Import preamble hierarchy.

#[local] Open Scope nat_scope.
#[local] Open Scope monae_scope.

Create HintDb airlock.

(** * Specifying *)

(** ** Doors *)

Inductive door : Type := left | right.

Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Generalizable All Variables.

Arguments request {_ } _ _ _.

Section a.

Definition is_open `{Provide ix DOORS} {im : impureMonad ix} (d : door) :
    im bool :=
  trigger (inj_p $ IsOpen d).

Definition toggle `{Provide ix DOORS} {im : impureMonad ix} (d : door) :
    im unit :=
  trigger (inj_p $ Toggle d).

Definition open_door `{Provide ix DOORS} {im : impureMonad ix}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when (negb open) (toggle d).

Definition close_door `{Provide ix DOORS} {im : impureMonad ix}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} {im : impureMonad ix} : im unit :=
  trigger (inj_p Tick).

Definition request_open `{Provide ix CONTROLLER} {im : impureMonad ix}
    (d : door) : im unit :=
  trigger (inj_p $ RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)}
    {im : impureMonad ix} : component (im:=im) CONTROLLER ix
  (* .
  move=>X; case=>[|d].
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
      when (15 <? cpt) $
        close_door left >>
        close_door right >>
        iput 0
    | RequestOpen d =>
        close_door (co d) >>
        open_door d >>
        iput 0
    end.

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(** *** Witness States *)

Definition Ω : Type := bool * bool.

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = negb (sel d ω).

Proof.
  by case:d.
Qed.

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

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

(** *** Requirements *)

Inductive doors_o_caller : Ω -> forall (a : Type), DOORS a -> Prop :=

(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)

| req_is_open (d : door) (ω : Ω)
  : doors_o_caller ω bool (IsOpen d)

(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed too for a request to toggle [d] to be valid. *)

| req_toggle (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : doors_o_caller ω unit (Toggle d).

Hint Constructors doors_o_caller : airlock.

(** *** Promises *)

Inductive doors_o_callee : Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| doors_o_callee_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : doors_o_callee ω bool (IsOpen d) x

(** - There is no particular requirement on the result [x] of a request for
      [ω] to close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

 Hint Constructors doors_o_callee : airlock.

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

(** ** Intermediary Lemmas *)

Lemma doors_is_open_calleeE (ω : Ω) (d : door) (x : bool) :
  doors_o_callee ω bool (IsOpen d) x -> sel d ω = x.
Proof.
move=> reported.
by inversion reported; ssubst.
Qed.

Lemma doors_toggle_callerE (ω : Ω) (d : door) :
  doors_o_caller ω unit (Toggle d) ->
  sel d ω = false -> sel (co d) ω = false.
Proof.
move=> allowed.
by inversion allowed as [d' ω' | d' ω' safe]; subst.
Qed.

(** Closing a door [d] in any system [ω] is always a respectful operation. *)

Lemma close_door_respectful `{Provide ix DOORS} (ω : Ω) (d : door) :
  pre (to_hoare
         (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
         doors_contract (close_door d)) ω.

Proof.
rewrite /close_door /is_open.
apply/to_hoare_request_then_preI.
- rewrite /gen_caller_obligation proj_inj_p_equ /=.
  exact: req_is_open.
move=> opened.
rewrite /gen_callee_obligation /gen_witness_update !proj_inj_p_equ /=.
move=> reported.
have reported_equ := doors_is_open_calleeE ω d opened reported.
clear reported.
case: opened reported_equ => reported_equ.
- rewrite /when /toggle.
  apply/to_hoare_request_then_preI.
  + rewrite /gen_caller_obligation proj_inj_p_equ /=.
    apply: req_toggle => closed.
    by rewrite reported_equ in closed.
  + move=> toggle_result _.
    exact: to_hoare_local_preI.
rewrite /when.
exact: to_hoare_local_preI.

  (* This leaves us with one goal to prove:

       [sel d ω = false -> sel (co d) ω = false]

     Yet, thanks to our call to [IsOpen d], we can predict that

       [sel d ω = true] *)

Qed.

 Hint Resolve close_door_respectful : airlock.

Lemma open_door_respectful `{Provide ix DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false) :
  pre (to_hoare
         (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
         doors_contract (open_door (ix := ix) d)) ω.

Proof.
rewrite /open_door /is_open.
apply/to_hoare_request_then_preI.
  - rewrite /gen_caller_obligation proj_inj_p_equ /=.
    exact: req_is_open.
move=> opened.
rewrite /gen_callee_obligation /gen_witness_update !proj_inj_p_equ /=.
move=> reported.
have reported_equ := doors_is_open_calleeE ω d opened reported.
clear reported.
case: opened reported_equ => reported_equ.
  - rewrite /when.
    exact: to_hoare_local_preI.
rewrite /when /toggle.
apply/to_hoare_request_then_preI.
  - rewrite /gen_caller_obligation proj_inj_p_equ /=.
    by apply: req_toggle.
move=> toggle_result _.
exact: to_hoare_local_preI.
Qed.

 Hint Resolve open_door_respectful : airlock.

Lemma store_request_preI `{StrictProvide2 ix DOORS (STORE nat)}
    `(e : STORE nat a) (ω : Ω) :
  pre (to_hoare
         (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
         doors_contract
         (@request ix
           (ImpureModule_acto__canonical__Impure_MonadImpure ix)
           a (inj_p e))) ω.
Proof.
by apply/to_hoare_request_preE; rewrite /gen_caller_obligation distinguish.
Qed.

Lemma doors_is_open_postE `{Provide ix DOORS} (ω : Ω) (d : door)
    (opened : bool) (ω' : Ω) :
  post (to_hoare
          (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
          doors_contract (is_open d)) ω opened ω' ->
  sel d ω = opened /\ ω' = ω.
Proof.
rewrite /is_open.
move=> /to_hoare_request_postE [reported witness].
rewrite /gen_callee_obligation proj_inj_p_equ /= in reported.
rewrite /gen_witness_update proj_inj_p_equ /= in witness.
split.
- exact: doors_is_open_calleeE ω d opened reported.
- exact: witness.
Qed.

Lemma doors_toggle_postE `{Provide ix DOORS} (ω : Ω) (d : door)
    (result : unit) (ω' : Ω) :
  post (to_hoare
          (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
          doors_contract (toggle d)) ω result ω' ->
  ω' = tog d ω.
Proof.
rewrite /toggle.
move=> /to_hoare_request_postE. move=> [_ witness].
by rewrite /gen_witness_update proj_inj_p_equ /= in witness.
Qed.

Lemma close_door_run `{Provide ix DOORS} (ω : Ω) (d : door)
    (ω' : Ω) (x : unit)
    (run : post (to_hoare
      (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
      doors_contract (close_door d)) ω x ω') :
  sel d ω' = false.
Proof.
  rewrite /close_door in run.
  move: run => /to_hoare_bind_postE [open [ω1 [opened tail]]].
  move: opened => /doors_is_open_postE [reported witness].
  subst ω1.
  case is_open_equ: (sel d ω) reported tail => reported tail.
  - cbn in tail.
    have open_true : open = true := eq_sym reported.
    rewrite open_true in tail.
    cbn in tail.
    move: tail => /to_hoare_bind_postE
      [toggle_result [ω2 [toggle_run done]]].
    move: toggle_run => /doors_toggle_postE toggle_witness.
    move: done => /to_hoare_local_postE [_ local_witness].
    subst ω2; subst ω'.
    by rewrite tog_equ_1 is_open_equ.
  have open_false : open = false := eq_sym reported.
  rewrite open_false in tail.
  cbn in tail.
  move: tail => /to_hoare_local_postE [_ witness].
  subst ω'.
  exact: is_open_equ.
Qed.

 Hint Resolve close_door_run : airlock.

#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : sel d ω = false \/ sel (co d) ω = false)
  : forall (d' : door), sel d' ω = false \/ sel (co d') ω = false.

Proof.
  intros d'.
  destruct d; destruct d'; auto.
  + cbn -[sel].
    now rewrite or_comm.
  + cbn -[sel].
    fold (co right).
    now rewrite or_comm.
Qed.

(** The objective of this lemma is to prove that, if either the right door or
    the left door is closed, then after any respectful run of a computation
    [p] that interacts with doors, this fact remains true. *)

#[local] Opaque sel.

Lemma doors_request_preserves_safe {ix a}
    `{may_doors : MayProvide ix DOORS}
    `{provide_doors : @Provide ix DOORS may_doors} (e : ix a)
    (ω : Ω) (x : a) :
  @gen_caller_obligation ix DOORS may_doors Ω a
    doors_contract ω e ->
  @gen_callee_obligation ix DOORS may_doors Ω a
    doors_contract ω e x ->
  (sel left ω = false \/ sel right ω = false) ->
  sel left (@gen_witness_update ix DOORS may_doors Ω a
    doors_contract ω e x) = false \/
  sel right (@gen_witness_update ix DOORS may_doors Ω a
    doors_contract ω e x) = false.
Proof.
case projected: (@proj_p ix DOORS may_doors a e) => [door_request |].
  rewrite /gen_caller_obligation /gen_callee_obligation
    /gen_witness_update projected /=.
  clear projected.
  case: door_request x => d x caller callee safe.
  - exact: safe.
  apply one_door_safe_all_doors_safe with (d := d).
  apply one_door_safe_all_doors_safe with (d' := d) in safe.
  move: safe => [closed | other_closed]; right; rewrite tog_equ_2.
    exact: doors_toggle_callerE ω d caller closed.
  exact: other_closed.
by rewrite /gen_caller_obligation /gen_callee_obligation
  /gen_witness_update projected.
Qed.

Lemma respectful_run_inv `{Provide ix DOORS} {A} (p : impure ix A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω)
    (hpre : pre (to_hoare
      (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
      doors_contract p) ω)
    (hpost : post (to_hoare
      (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
      doors_contract p) ω a ω') :
  sel left ω' = false \/ sel right ω' = false.

(** We reason by induction on the impure computation [p]:

    - Either [p] is a local, pure computation; in such a case, the doors state
      does not change, hence the proof is trivial.

    - Or [p] consists in a request to the doors interface, and a continuation
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
rewrite -co_leftE in safe hpre hpost |-*.
move: p ω hpre hpost safe.
elim=> [result | b e f ih] ω hpre run safe.
- move: run => /to_hoare_local_postE [_ witness].
  subst ω'.
  exact: safe.
move: run => /to_hoare_request_then_postE [x [step run]].
move: hpre => /to_hoare_request_then_preE [caller next].
apply: (ih x (gen_witness_update doors_contract ω e x)).
- exact: next step.
- exact: run.
exact: (doors_request_preserves_safe (ix := ix) (a := b) e ω x
          caller step safe).
Qed.

(** ** Main Theorem *)
Definition correct_component `{MayProvide jx j}
   `(c : component i jx) `(ci : contract i Ωi) `(cj : contract j Ωj)
    (pred : Ωi -> Ωj -> Prop)
  : Prop :=
   forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
         `(e : i α) (o_caller : caller_obligation ci ωi e),
    pre (to_hoare cj $ c α e) ωj /\
    forall (x : α) (ωj' : Ωj),
      post (to_hoare
        (im:=ImpureModule_acto__canonical__Impure_MonadImpure jx)
        cj (c α e)) ωj x ωj' ->
      callee_obligation ci ωi e x /\
      pred (witness_update ci ωi e x) ωj'.


Lemma gen_witness_update_otherE
    `{Provide ix i, MayProvide ix j, Distinguish ix i j}
    `(c : contract j Ω) (ω : Ω) `(e : i a) (x : a) :
  gen_witness_update c ω (inj_p e) x = ω.
Proof. by rewrite /gen_witness_update distinguish. Qed.


Lemma controller_correct `{StrictProvide2 ix DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).
Proof.
move=> ωc ωd safe A eff _.
(* clear request_ok. *)
have hpre :
    pre (to_hoare
           (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
           doors_contract (controller A eff)) ωd.
case: eff => [|d]; rewrite /controller/iget.
- apply: to_hoare_bind_preI.
  + exact: store_request_preI.
  + move=> x om /to_hoare_request_postE [_ +].
    rewrite (gen_witness_update_otherE (ix:=ix) (i:=STORE nat) (j:=DOORS))=> ->.
    case: (15 <? x) => //=.
    apply: to_hoare_bind_preI=> //.
    apply: to_hoare_bind_preI.
      * by apply: to_hoare_bind_preI=> [|???]; exact/close_door_respectful.
      * by move=> ???; exact: store_request_preI.
- apply: to_hoare_bind_preI.
  + apply: to_hoare_bind_preI.
    * exact: close_door_respectful.
    * move=> ?? close_run; apply: open_door_respectful.
      exact: close_door_run close_run.
  + by move=> ???; exact: store_request_preI.
split=> //?? run; split=> //.
exact: respectful_run_inv _ _ safe _ _ hpre run.
Qed.

End a.
