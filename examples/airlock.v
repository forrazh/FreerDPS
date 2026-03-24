(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From Coq Require Import Arith.
From FreerDPS Require Import Core Impure Hoare.
From monae Require Import preamble hierarchy.
From mathcomp Require Import ssreflect.

#[local] Open Scope nat_scope.
#[local] Open Scope monae_scope.

Create HintDb airlock.

(** * Specifying *)

(** ** Doors *) 

Locate not_locked_false_eq_true.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | simple refine (@sym_equal _ _ _ _); trivial]
         | discriminate | contradiction | split]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end 
   | auto with freespec
   ].
Inductive door : Type := left | right.
 
Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Generalizable All Variables.

Arguments request {_ } _ _ _.

Check request.

Section a.

Definition is_open `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im bool := trigger (inj_p $ IsOpen d).

Definition toggle `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im unit := trigger (inj_p $ Toggle d).

Definition open_door `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im unit :=
  is_open d >>= fun open =>
  when (negb open) (toggle d).

Definition close_door `{Provide ix DOORS} {im : impureMonad ix} (d : door) : im unit :=
  is_open d >>= fun open =>
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} {im : impureMonad ix} : im unit :=
  trigger (inj_p Tick).

Definition request_open `{Provide ix CONTROLLER} {im : impureMonad ix}  (d : door) : im unit :=
  trigger (inj_p $ RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Check (forall i, component CONTROLLER i).

Search iget.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)} {im : impureMonad ix}
  : component (im:=im) CONTROLLER ix
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

Lemma close_door_respectful `{Provide ix DOORS} {im : impureMonad ix} (ω : Ω) (d : door)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (doors_contract) (close_door d))( ω).

Proof.
  do ! [prove impure with airlock; subst; constructor].

  (* This leaves us with one goal to prove:

       [sel d ω = false -> sel (co d) ω = false]

     Yet, thanks to our call to [IsOpen d], we can predict that

       [sel d ω = true] *)

  inversion o_caller0; ssubst.
  now rewrite H3.
Qed.

 Hint Resolve close_door_respectful : airlock.

Lemma open_door_respectful `{Provide ix DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) doors_contract (open_door (ix := ix) d)) ω.

Proof.
  do ! [prove impure; repeat constructor; subst].
  (* inversion o_caller0; ssubst. *)
Qed.

 Hint Resolve open_door_respectful : airlock.

Lemma to_hoare_post_bind_assoc `{MayProvide ix i} `(c : contract i Ω)
   `(p : impure ix a) `(f : a -> impure ix b)
   `(Hp : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (impure_bind p f)) ω x ω')
  : exists y ω'',
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c p) ω y ω'' /\ post (to_hoare c (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) $ f y) ω'' x ω'.

Proof.
move: ω Hp; elim p=>[in_a|Y j k IH] ω.
- by exists in_a, ω.
case=>y [ω'' [Hp1 ]].
move:IH=>/[apply].
move=> [z [ω''' [Hp2 Hp3]]].
exists z, ω'''.
split=>//.
exists y, ω''.
by split.

Qed.


Ltac run_simpl run := do ? [cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
] in *; simplify_gens; do ? destruct_if_when_in run]; lazymatch type of run with
| post (to_hoare ?c ?p) ?ω ?x ?ω' => 
  let p := (eval hnf in p) in
  lazymatch p with
  | request_then ?e ?f => 
    inversion run; ssubst; let old_run := fresh "old_run" in move: run=>old_run;
    lazymatch goal with
    | next : exists _, post (interface_to_hoare c (A:=_) e) _ _ _ /\ _ |- _ => let ω'' := fresh "ω" in let o_callee := fresh "o_calleeeeeeeee" in let run := fresh "run" in case next =>/=ω'' [o_callee run]; run_simpl run 
    | next : post (lifter (i:=_) (M:=_) _ _) _ _ _ |- _ => have Hfucked : 1 = 3
    | _ => have Hfucked : 1 = 1
    end
  | local ?x => let old_run := fresh "old_run" in inversion run; ssubst; move:run=>old_run; have Hfucked : 3 = 3
  | impure_bind ?p ?f => move: run=>nooo
      (* apply (to_hoare_post_bind_assoc c p f) in run;
      let run1 := fresh "run" in
      let run2 := fresh "run" in
      let x := fresh "x" in
      let ω := fresh "ω" in
      destruct run as [x [ω [run1 run2]]];
      unroll_post run1; unroll_post run2 *)
  end
| post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (bind ?f ?x)) _ _ _  => apply (bindA f x) in run

| ?a => have Hfucked : 2 = 2
end.

(* lazymatch goal with
  | next : exists _, post (interface_to_hoare c _ _) _ _ _ /\ _ |- _ =>
    let ω'' := fresh "ω" in
    let o_callee := fresh "o_callee" in
    let run := fresh "run" in
    case next =>/=ω'' [o_callee run];
    run_simpl run
  | _ => idtac
  end *)

(* Lemma post_lifted_proper :  forall (N : monad) (l : forall A : UU0, ?i A -> N A) (X Y : UU0)
(m :N X) (f : X -> ?s Y),
impure_lift N l Y (m >>= f) = impure_lift N l X m >>=
(fun x0 : X => impure_lift N l Y (f x0)) . *)

Lemma close_door_run `{Provide ix DOORS} (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) doors_contract (close_door d)) ω x ω')
  : sel d ω' = false.
Proof.
  Check impure_lift_bind.
  (* rewrite bindA in run. *)
  (* run_simpl run. inversion run; ssubst; move: run H4=>_; case=>/=b [a run].
  run_simpl run. fold to_hoare in run. rewrite impure_lift_bind in run. destruct_if_when_in run. move:run=>_.
  inversion run; ssubst. move:run; apply/impure_lift_bind. Check lifter (i:=_) (M:=_) _ _. 
  inversion new_run;ssubst; move: new_run=>_.
  - run_simpl run.  inversion run; ssubst; move:run; case=>/=ω'' [o_callee run].
    run_simpl run; 
    ssubst. 

    by inversion H1; ssubst; rewrite tog_equ_1 H5.
  - inversion run; ssubst; move:run H1=>_ H1.

 by inversion H1; ssubst. *)
Admitted.


Proof.
    (* do ! [rewrite /= in run; simplify_gens ; destruct_if_when_in run]. *)
    unroll_post run. 
    

  (* do ! [unroll_post run; rewrite /= in run; ssubst];  inversion run; rewrite /= in run; ssubst. *)
  - inversion H1; ssubst. repeat destruct H3; ssubst.
  destruct  H; ssubst. 
    rewrite tog_equ_1.
    inversion H1; ssubst.
    now rewrite H6.
  + now inversion H1; ssubst.
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

Lemma respectful_run_inv `{Provide ix DOORS} {A} (p : impure ix A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω) 
    (hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) doors_contract p) ω)
    (hpost: post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) doors_contract p) ω a ω')
  : sel left ω' = false \/ sel right ω' = false.

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
  fold (co left) in *.
  revert ω hpre hpost safe.
  (* elim p=>[a'|B e f IH] ω pre run safe. *)
  induction p; intros ω hpre run safe.
  + by unroll_post run.
  + unroll_post run. 
    assert (hpost : post (interface_to_hoare doors_contract β e) ω x ω0). {
      split ; [apply H2|now rewrite H3].
    }
    apply H1 in run; auto; [by apply hpre|].
      (* * subst=>/=. inversion H2;subst. ssubst. *)
       (* destruct d=>//=. apply/  with (ω:=ω0) (β:=x). auto; [now apply hpre|]. *)
    (* apply H1 with (ω:=ω0) (β:=x); auto. [now apply hpre|].     *)
    cbn in *.
    (* rewrite -bindA in hpre. *)
    (* inversion hpre. *)
    inversion hpre; rewrite /=/gen_caller_obligation in H4.

    unfold lifter, gen_caller_obligation, gen_callee_obligation, gen_witness_update in *. 
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

  (* revert ω hpre hpost safe. *)
  (* induction p; intros ω hpre run safe. *)
  (* + now unroll_post run. *)
  (* + unroll_post run. *)
    (* assert (hpost : post (interface_to_hoare doors_contract β e) ω x0 ω0). { *)
      (* split; [apply H2|now rewrite H3]. *)
    (* } *)
    (* apply H1 with (ω:=ω0) (β:=x0); auto; [now apply hpre|]. *)
    (* cbn in *. *)
    (* unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *. *)
    (* destruct (proj_p e) as [e'|]. *)
    (* ++ destruct hpost as [o_callee equω]. *)
       (* destruct e' as [d|d]. *)
       (* +++ rewrite H3. *)
           (* apply safe. *)
       (* +++ apply one_door_safe_all_doors_safe with (d := d); *)
             (* apply one_door_safe_all_doors_safe with (d' := d) in safe; *)
             (* subst. *)
           (* destruct hpre as [hbefore hafter]. *)
           (* inversion hbefore; ssubst. *)
           (* cbn. *)
           (* destruct safe as [safe|safe]. *)
           (* all: right; rewrite tog_equ_2; auto. *)
    (* ++ destruct hpost as [_ equω]. *)
       (* subst. *)
       (* exact safe. *)
(* Qed. destruct safe.  ; auto. *)
    (* ++ destruct hpost as [_ equω]. *)
       (* subst. *)
       (* exact safe. *)
(* Qed. *)



  (* fold (co left) in *.
  move: ω hpre hpost safe.
  elim: p=>[x' | β eff k IH] ω hpre run safe.
  (* induction p; intros ω hpre run safe. *)
  + by unroll_post run.
  + unroll_post run.
    assert (hpost : post (interface_to_hoare doors_contract β eff) ω x0 ω0). {
      split; [apply H1|now rewrite H2].
    }
    apply IH with (ω:=ω0) (β:=x0) => // ; [now apply hpre|] => //=.
    (* move: H1 run H2 hpost => /gen_caller_obligation/gen_callee_obligation/gen_witness_update H1 run H2 hpost. *)
    unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *.
    (* move: H1 H2; case: (proj_p eff) => [e'|] H1 H2. *)
    destruct (proj_p eff) as [e'|] eqn:E.
    ++ destruct hpost as [o_callee equω].
      case e' => d/=.
       destruct e' as [d|d].
       +++ rewrite H2.
           apply safe.

       +++ apply one_door_safe_all_doors_safe with (d := d);
             apply one_door_safe_all_doors_safe with (d' := d) in safe;
             subst.
           destruct hpre as [hbefore hafter].
           (* inversion hpre; ssubst=>//=. *)
           inversion hbefore; ssubst.
           destruct safe as [safe|safe].
           (* ; case Ed: d; rewrite Ed in safe => //=. *)
           - right; rewrite tog_equ_2/=; auto. admit.
           - by right; rewrite tog_equ_2. 
           
            (* .  Check tog_equ_1. *)
      ++ rewrite H2; exact: safe. *)
              (* inversion o_callee; ssubst. *)
              (* inversion safe. *)
              (* prove impure with airlock. *)
              (* auto. *)
           (*  *)
           (* admit. *)

  (* all: inversion H1; ssubst.  *)
   (* rewrite /= in run. ; firstorder.  *)
    (* ++ destruct hpost as [_ equω].
       subst.
       exact safe. *)
Qed.

(** ** Main Theorem *)
Definition correct_component `{MayProvide jx j}
   `(c : component i jx) `(ci : contract i Ωi) `(cj : contract j Ωj)
    (pred : Ωi -> Ωj -> Prop)
  : Prop :=
   forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
         `(e : i α) (o_caller : caller_obligation ci ωi e),
    pre (to_hoare cj $ c α e) ωj /\
    forall (x : α) (ωj' : Ωj) (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure jx) cj $ c α e) ωj x ωj'),
      callee_obligation ci ωi e x /\ pred (witness_update ci ωi e x) ωj'.

Lemma controller_correct `{StrictProvide2 ix DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).
Proof.
  move=>ωc ωd pred A eff req. 
  have hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) doors_contract (controller A eff)) ωd.
    { 
      case eff=> [|d]//=; do ! [prove impure with airlock; ssubst; constructor=>//=]. 
      - by inversion o_caller; ssubst; rewrite H6.
      - by inversion o_caller1; ssubst; rewrite H6.
      - by inversion o_caller0; ssubst; rewrite H6.
      - by inversion o_caller; ssubst; rewrite H6.
      - by inversion o_caller1; ssubst;inversion o_caller; ssubst; rewrite H6 tog_equ_1/=H7.
      - by inversion o_caller; ssubst.
    }
  
  split=>[|a ωj' run]//=;
  split=>//=.
  Check respectful_run_inv.
  (* have run' := . *)
  by apply/(respectful_run_inv _ _ _ _ _ _ run). 
  (* apply respectful_run_inv in run => //=. *)
Qed.
