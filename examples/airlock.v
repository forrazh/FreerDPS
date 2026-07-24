(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From Coq Require Import Arith.
From FreerDPS Require Import Init.
From FreerDPS Require Import Core Impure Hoare.

#[local] Open Scope nat_scope.
#[local] Open Scope monae_scope.

Create HintDb airlock.

(** * Specifying *)

(** ** Doors *)

Inductive door : Type := left | right.

Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : effect :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Generalizable All Variables.

Arguments request {_ } _ _ _.

Check request.

Section a.

Definition is_open `{Provide Fx DOORS} {im : impureMonad Fx} (d : door) : im bool := trigger (inj_p $ IsOpen d).

Definition toggle `{Provide Fx DOORS} {im : impureMonad Fx} (d : door) : im unit := trigger (inj_p $ Toggle d).

Definition open_door `{Provide Fx DOORS} {im : impureMonad Fx} (d : door) : im unit :=
  is_open d >>= fun open =>
  when (negb open) (toggle d).

Definition close_door `{Provide Fx DOORS} {im : impureMonad Fx} (d : door) : im unit :=
  is_open d >>= fun open =>
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : effect :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide Fx CONTROLLER} {im : impureMonad Fx} : im unit :=
  trigger (inj_p Tick).

Definition request_open `{Provide Fx CONTROLLER} {im : impureMonad Fx}  (d : door) : im unit :=
  trigger (inj_p $ RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Definition controller `{Provide Fx DOORS, Provide Fx (STORE nat)} {im : impureMonad Fx}
  : component (im:=im) CONTROLLER Fx
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

Proof.
  destruct d; reflexivity.
Qed.

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

(** - There is no particular doors_o_calleeises on the result [x] of a request for [ω] to
      close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

 Hint Constructors doors_o_callee : airlock.

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

(** ** Intermediary Lemmas *)

(** Closing a door [d] in any system [ω] is always a respectful operation. *)

Lemma close_door_respectful `{Provide Fx DOORS} {im : impureMonad Fx} (ω : Ω) (d : door)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) (doors_contract) (close_door d))( ω).

Proof.
  prove impure with airlock; subst ; constructor.

  (* This leaves us with one goal to prove:

       [sel d ω = false -> sel (co d) ω = false]

     Yet, thanks to our call to [IsOpen d], we can predict that

       [sel d ω = true] *)

  inversion o_caller0; ssubst.
  now rewrite H3.
Qed.

 Hint Resolve close_door_respectful : airlock.

Lemma open_door_respectful `{Provide Fx DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) doors_contract (open_door (Fx := Fx) d)) ω.

Proof.
  prove impure; repeat constructor; subst.
  by inversion o_caller0; ssubst.
Qed.

 Hint Resolve open_door_respectful : airlock.

Lemma close_door_run `{Provide Fx DOORS} (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) doors_contract (close_door d)) ω x ω')
  : sel d ω' = false.
Proof.
  run_simpl run;
  cleanvert H1.
  cleanvert run.
  cleanvert H1.
  run_simpl H2.

  cleanvert H2.
  (* cleanvert H4. *)

  -  cleanvert H1.
    by rewrite tog_equ_1 H5.
  by  cleanvert run.
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

Lemma respectful_run_inv `{Provide Fx DOORS} {A} (p : impure Fx A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω)
    (hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) doors_contract p) ω)
    (hpost: post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) doors_contract p) ω a ω')
  : sel left ω' = false \/ sel right ω' = false.

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
  fold (co left) in *.
  revert ω hpre hpost safe.
  (* elim p=>[a'|B e f IH] ω pre run safe. *)
  induction p; intros ω hpre run safe.
  + by unroll_post run.
  + run_simpl run.
    have hpost : post (hoare_of_contract doors_contract (A:=β) e) ω x ω0
      by split; [apply H2| by rewrite H3].
    (* move: H1 => /(_ x ω0) => H1. *)
     apply/(H1 x ω0) => //; [by apply hpre|].
    cbn in *.
    inversion hpre; rewrite /=/gen_caller_obligation in H4.
    (* simplify_gens *)
    unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *.
    cbn in *.
    destruct (proj_p e) as [e'|].
    ++ destruct hpost as [o_callee equω].
       destruct e' as [d|d].
       +++ rewrite H3.
           apply safe.
       +++ apply one_door_safe_all_doors_safe with (d := d);
             apply one_door_safe_all_doors_safe with (d' := d) in safe;
             subst.
             inversion H4.
           cbn.
           by destruct safe as [safe|safe];
            right; rewrite tog_equ_2//.
    ++ rewrite H3;
       exact: safe.
Qed.

(** ** Main Theorem *)
Definition correct_component `{MayProvide Ex E}
   `(c : component F Ex) `(ci : contract F ΩF) `(cj : contract E ΩE)
    (pred : ΩF -> ΩE -> Prop)
  : Prop :=
   forall (ωF : ΩF) (ωE : ΩE) (init : pred ωF ωE)
         `(e : F α) (o_caller : caller_obligation ci ωF e),
    pre (to_hoare cj $ c α e) ωE /\
    forall (x : α) (ωE' : ΩE) (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Ex) cj $ c α e) ωE x ωE'),
      callee_obligation ci ωF e x /\ pred (witness_update ci ωF e x) ωE'.



Lemma controller_correct `{StrictProvide2 Fx DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).
Proof.
  move=>ωc ωd pred A eff req.
  have hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure Fx) doors_contract (controller A eff)) ωd.
    {
      case eff; do ! [prove impure with airlock; ssubst; constructor => //].


      (* case eff=> [|d]//; prove impure with airlock; ssubst; constructor=>//. *)
        (* do ! [prove impure with airlock; ssubst; constructor=>//=].  *)
      - by inversion o_caller; ssubst; rewrite H6.
      - by inversion o_caller1; ssubst; rewrite H6.
      - by inversion o_caller0; ssubst; rewrite H6.
      - by inversion o_caller; ssubst; rewrite H6.
      - by inversion o_caller1; ssubst;inversion o_caller; ssubst; rewrite H6 tog_equ_1/=H7.
      - by inversion o_caller; ssubst.
    }

  split=>[|a ωE' run]//=;
  split=>//=.
  by apply/(respectful_run_inv _ _ _ _ _ _ run).
Qed.

End a.
