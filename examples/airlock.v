(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From Stdlib Require Import Arith.
From mathcomp Require Import all_boot boolp.
From FreerDPS Require Import Core Impure Hoare HoareFacts.
From monae Require Import preamble hierarchy.

#[local] Open Scope nat_scope.
#[local] Open Scope monae_scope.

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

Definition is_open `{Provide ix DOORS} {im : freerMonad ix} (d : door) :
    im bool :=
  trigger $ IsOpen d.

Definition toggle `{Provide ix DOORS} {im : freerMonad ix} (d : door) :
    im unit :=
  trigger $ Toggle d.

Definition open_door `{Provide ix DOORS} {im : freerMonad ix}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when (~~ open) (toggle d).

Definition close_door `{Provide ix DOORS} {im : freerMonad ix}
    (d : door) : im unit :=
  is_open d >>= fun open =>
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} {im : freerMonad ix} : im unit :=
  trigger Tick.

Definition request_open `{Provide ix CONTROLLER} {im : freerMonad ix}
    (d : door) : im unit :=
  trigger $ RequestOpen d.

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Lemma co_leftE : co left = right.
Proof. by []. Qed.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)}
    {im : freerMonad ix} : component (im:=im) CONTROLLER ix
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

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

(** ** Intermediary Lemmas *)

Lemma doors_is_open_calleeE (ω : Ω) (d : door) (x : bool) :
  doors_o_callee ω bool (IsOpen d) x -> sel d ω = x.
Proof. by case: x=> postc; inversion postc; ssubst. Qed.

Lemma doors_toggle_callerE (ω : Ω) (d : door) :
  doors_o_caller ω unit (Toggle d) ->
  sel d ω = false -> sel (co d) ω = false.
Proof.
by move=> allowed; inversion allowed as [d' ω' | d' ω' safe]; subst.
Qed.

(** Closing a door [d] in any system [ω] is always a respectful operation. *)

Lemma close_door_respectful `{Provide ix DOORS} (ω : Ω) (d : door) :
  pre (to_hoare (im:=freer ix) doors_contract (close_door d)) ω.
Proof.
rewrite /close_door /is_open.
apply/to_hoare_impure_preI=> [|opened].
- by rewrite /gen_caller_obligation proj_inj_p_equ /=; exact: req_is_open.
rewrite /gen_callee_obligation /gen_witness_update !proj_inj_p_equ /=.
move=> isopen_post.
have isopen_post_equ := doors_is_open_calleeE ω d opened isopen_post.
move: isopen_post isopen_post_equ=> _.
rewrite /when /toggle; case: opened=> isopen_post_equ; last first.
- exact: to_hoare_skip_preI.
apply/to_hoare_impure_preI.
- rewrite /gen_caller_obligation proj_inj_p_equ /=; apply: req_toggle.
  by rewrite isopen_post_equ.
- by move=> *; exact: to_hoare_skip_preI.
Qed.

Lemma open_door_respectful `{Provide ix DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false) :
  pre (to_hoare (im:=freer ix) doors_contract (open_door (ix := ix) d)) ω.
Proof.
rewrite /open_door /is_open.
apply/to_hoare_impure_preI.
- rewrite /gen_caller_obligation proj_inj_p_equ /=.
  exact: req_is_open.
move=> opened.
rewrite /gen_callee_obligation /gen_witness_update !proj_inj_p_equ /=.
move=> isopen_post.
have isopen_post_equ := doors_is_open_calleeE ω d opened isopen_post.
move: isopen_post=>_.
case: opened isopen_post_equ => isopen_post_equ.
- rewrite /when.
  exact: to_hoare_skip_preI.
rewrite /when /toggle.
apply/to_hoare_impure_preI.
- rewrite /gen_caller_obligation proj_inj_p_equ /=.
  by apply: req_toggle.
move=> toggle_result _.
exact: to_hoare_skip_preI.
Qed.

Lemma store_request_preI `{StrictProvide2 ix DOORS (STORE nat)}
    `(e : STORE nat a) (ω : Ω) :
  pre (to_hoare (im:=freer ix) doors_contract (trigger e)) ω.
Proof.
by apply/to_hoare_request_preE; rewrite /gen_caller_obligation /= distinguish.
Qed.

Lemma doors_is_open_postE `{Provide ix DOORS} (ω : Ω) (d : door)
    (opened : bool) (ω' : Ω) :
  post (to_hoare (im:=freer ix)doors_contract (is_open d)) ω opened ω' ->
  sel d ω = opened /\ ω' = ω.
Proof.
rewrite /is_open to_hoare_request_postE /gen_callee_obligation /gen_witness_update.
rewrite proj_inj_p_equ /= => -[w po].
split.
- exact: doors_is_open_calleeE ω d opened po.
- exact: w.
Qed.

Lemma doors_toggle_postE `{Provide ix DOORS} (ω : Ω) (d : door)
    (result : unit) (ω' : Ω) :
  post (to_hoare (im:=freer ix) doors_contract (toggle d)) ω result ω' ->
  ω' = tog d ω.
Proof.
rewrite /toggle to_hoare_request_postE /gen_witness_update proj_inj_p_equ /=.
by move=> [-> _].
Qed.

Lemma close_door_run `{Provide ix DOORS} (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (to_hoare (im:=freer ix) doors_contract (close_door d)) ω x ω') :
sel d ω' = false.
Proof.
move: run.
rewrite /close_door to_hoare_bind_postE.
move=>[opened [? []]]=> /doors_is_open_postE [+ ->]/=.
case is_open_equ: (sel d ω)=> <-; last first.
- by rewrite to_hoare_local_postE=> -[_ <-].
rewrite to_hoare_bind_postE=> -[a [w' [/doors_toggle_postE +]]].
move=> -> /to_hoare_local_postE [_ <-].
by rewrite tog_equ_1 is_open_equ.
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
- cbn -[sel].
  now rewrite or_comm.
- cbn -[sel].
  fold (co right).
  now rewrite or_comm.
Qed.

(** The objective of this lemma is to prove that, if either the right door or
    the left door is closed, then after any respectful run of a computation
    [p] that interacts with doors, this fact remains true. *)

#[local] Opaque sel.
Definition doors_safe (ω : Ω) :=
  sel left ω = false \/ sel right ω = false.

Lemma doors_request_preserves_safe {ix a} {mp : MayProvide ix DOORS}
    {provided : @Provide ix DOORS mp}
    (e : ix a) (ω : Ω) (x : a) (ω' : Ω) :
  pre (to_hoare (im:=freer ix) doors_contract (trigger e)) ω ->
  post (to_hoare (im:=freer ix) doors_contract (trigger e)) ω x ω' ->
  doors_safe ω -> doors_safe ω'.
Proof.
case projected: (@proj_p ix DOORS mp a e) => [door_request |];
rewrite to_hoare_request_preE to_hoare_request_postE;
rewrite /gen_caller_obligation /gen_callee_obligation /gen_witness_update
  projected //=; last first.
- by move=> _ [-> _].

move: door_request projected x=> + _.
case=> d x prec postc safe; apply one_door_safe_all_doors_safe with (d := d);
  apply one_door_safe_all_doors_safe with (d' := d) in safe;
  case: postc=> [-> postc] //.
case: safe=> [left_safe | right_safe]; right; rewrite tog_equ_2 //=.
exact: doors_toggle_callerE.
Qed.

Lemma respectful_run_inv `{Provide ix DOORS} {A} (p : freer ix A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω)
    (hpre : pre (to_hoare (im:=freer ix) doors_contract p) ω)
    (hpost : post (to_hoare (im:=freer ix) doors_contract p) ω a ω') :
  sel left ω' = false \/ sel right ω' = false.
(** We reason by induction on the impure computation [p]:

    - Either [p] is a local, pure computation; in such a case, the doors state
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
rewrite -co_leftE in safe hpre hpost |-*.
move: p ω hpre hpost safe.
elim=> [result | b e f ih] ω + + safe.
- rewrite to_hoare_local_postE=> ? [_ witness].
  subst ω'.
  exact: safe.
rewrite to_hoare_impure_preE to_hoare_impure_postE.
move=> [caller next] [x [run step]].
apply: (ih x (gen_witness_update doors_contract ω e x)).
- exact: next step.
- exact: run.
- apply: (doors_request_preserves_safe e ω x).
  + exact/to_hoare_request_preE.
  + exact: to_hoare_request_postI step.
  + exact: safe.
Qed.

(** ** Main Theorem *)
Definition correct_component `{MayProvide jx j}
    `(c : component i jx) `(ci : contract i Ωi) `(cj : contract j Ωj)
    (pred : Ωi -> Ωj -> Prop) :
  Prop :=
  forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
      `(e : i α) (o_caller : caller_obligation ci ωi e),
    pre (to_hoare cj $ c α e) ωj /\
    forall (x : α) (ωj' : Ωj),
      post (to_hoare
        (im:=freer jx)
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
have hpre : pre (to_hoare (im:=freer ix) doors_contract (controller A eff)) ωd.
case: eff => [|d]; rewrite /controller/iget.
- apply: to_hoare_bind_preI.
  + exact: store_request_preI.
  + move=> x om /to_hoare_request_postE [+ _].
    rewrite (gen_witness_update_otherE (ix:=ix) (i:=STORE nat)
      (j:=DOORS))=> ->.
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

End airlock_s.
