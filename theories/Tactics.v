(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* From ExtLib Require Import Monad. *)
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Init Interface Contract Impure Hoare HoareFacts.

Ltac destruct_if_when :=
  let equ_cond := fresh "equ_cond" in
  match goal with
  | |- context[when (negb ?B) _] => destruct B eqn:equ_cond; cbn
  | |- context[when ?B _] => destruct B eqn:equ_cond; cbn
  | |- context[if (negb ?B) then _ else _] => destruct B eqn:equ_cond; cbn
  | |- context[if ?B then _ else _] => destruct B eqn:equ_cond; cbn
  | _ => fail 1
  end.

Ltac destruct_if_when_in hyp :=
  let equ_cond := fresh "equ" in
  match goal with
  | H : context[when (negb ?B) _] |- _ => destruct B eqn:equ_cond
  | H : context[when ?B _] |- _ => destruct B eqn:equ_cond
  | H : context[if (negb ?B) then _ else _] |- _ => destruct B eqn:equ_cond
  | H : context[if ?B then _ else _] |- _ => destruct B eqn:equ_cond
  | _ => fail 1
  end.

Ltac simplify_gens :=
  repeat match goal with
         | H : True |- _ =>
           clear H

         | H: _ /\ _ |- _ =>
           destruct H

         | |- context[@proj_p ?ix ?ix (refl_MayProvide ?ix) _ ?e] =>
           change (@proj_p ix ix (refl_MayProvide ix) _ e) with (Some e);
           cbn match;
           cbn beta

         | H: context[@proj_p ?ix ?ix (refl_MayProvide ?ix) _ ?e] |- _ =>
           change (@proj_p ix ix (refl_MayProvide ix) _ e) with (Some e) in H;
           cbn match in H;
           cbn beta in H

         | |- context[gen_witness_update _ _ _ _] =>
           unfold gen_witness_update;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_witness_update _ _ _ _] |- _ =>
           unfold gen_witness_update in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)

         | |- context[gen_caller_obligation ?c ?ω ?e] =>
           unfold gen_caller_obligation;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_caller_obligation ?c ?ω ?e] |- _ =>
           unfold gen_caller_obligation in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)

         | |- context[gen_callee_obligation ?c ?ω ?e ?x] =>
           unfold gen_callee_obligation;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_callee_obligation ?c ?ω ?e ?x] |- _ =>
           unfold gen_callee_obligation in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)
         end.

#[local]
Ltac destruct_option_match t :=
  lazymatch t with
  | context[(match ?x with
             | Some _ => _
             | None => _
             end)] =>
      let Hx := fresh "Hx" in
      destruct x as [?|] eqn:Hx
  end.


#[local]
Ltac prove_impure_by solver :=
  cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
              lifter
          ] in *;
  try unfold when in *;
  try unfold skip in *;
  simplify_gens;
  repeat destruct_if_when;
  lazymatch goal with

  | |- _ /\ _ =>
    split;
    prove_impure_by solver

  | |- forall _ _, _ /\ _ = _ -> _ =>
    let x := fresh "x" in
    let ω' := fresh "ω" in
    let o_caller := fresh "o_caller" in
    let equ := fresh "equ" in
    intros x ω' [o_caller equ];
    repeat rewrite -> equ in *; clear equ; clear ω';
    prove_impure_by solver

    | |- pre ?pcond ?ω =>
        tryif destruct_option_match ω then prove_impure_by solver else

    lazymatch pcond with 
      | lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) ?p => let p := (eval hnf in p) in
        lazymatch p with
        | request_then ?e ?f =>
          let o_caller := fresh "o_caller" in
          assert (o_caller : gen_caller_obligation c ω e) ; 
          [ prove_impure_by solver | constructor; prove_impure_by solver]
        | local _ => constructor
        | impure_bind (impure_bind ?p ?f) ?g =>
          rewrite (bindA p f g);
          prove_impure_by solver
        | bind ?p ?f =>
          apply to_hoare_pre_bind_assoc; [ solver
                                        | let x := fresh "x" in
                                          let ω' := fresh "ω" in
                                          let hpost := fresh "hpost" in
                                          intros x ω' hpost;
                                          prove_impure_by solver
                                        ]
        | _ => solver
        end

    | to_hoare ?c ?p => let p := (eval hnf in p) in
      lazymatch p with
      | request_then ?e ?f =>
        let o_caller := fresh "o_caller" in
        assert (o_caller : gen_caller_obligation c ω e) ; 
        [ prove_impure_by solver | constructor; prove_impure_by solver]
      | local _ => constructor
      | impure_bind (impure_bind ?p ?f) ?g =>
        rewrite (bindA p f g);
        prove_impure_by solver
      | bind ?p ?f =>
        apply to_hoare_pre_bind_assoc; [ solver
                                      | let x := fresh "x" in
                                        let ω' := fresh "ω" in
                                        let hpost := fresh "hpost" in
                                        intros x ω' hpost;
                                        prove_impure_by solver
                                      ]
      | _ => solver
      end
    | _ => solver
    end 
  | |- ?a =>
    solver

  end.

Ltac prove_impure := prove_impure_by ltac:(cbn; eauto with freespec).

Tactic Notation "prove" "impure" := prove_impure.
Tactic Notation "prove" "impure" "with" ident(db) :=
  prove_impure_by ltac:(cbn; eauto with freespec db).

Ltac cleanvert hyp := inversion hyp; ssubst; clear hyp.

Ltac unroll_post_core hrun :=
  cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
          ] in *;
  try unfold when in *;
  try unfold skip in *;
  simplify_gens;
  repeat destruct_if_when_in hrun;
  lazymatch type of hrun with

  | post (to_hoare ?c ?p) ?ω ?x ?ω' =>
    let p := (eval hnf in p) in
    lazymatch p with
    | request_then ?e ?f =>
      cleanvert hrun;
      lazymatch goal with
      | next : exists _, post _ _ _ _ /\ _ |- _ =>
        let ω'' := fresh "ω" in
        let o_callee := fresh "o_callee" in
        let run := fresh "run" in
        destruct next as [ω'' [o_callee run]]
      | _ => idtac
      end

    | local ?x =>
      cleanvert hrun

    | impure_bind ?p ?f =>
      let run1 := fresh "run" in
      let run2 := fresh "run" in
      let x := fresh "x" in
      let ω := fresh "ω" in
      let hbind := fresh "hbind" in
      pose proof (FreerDPS.HoareFacts.to_hoare_post_bind_assoc c p f hrun) as hbind;
      destruct hbind as [x [ω [run1 run2]]];
      clear hrun

    | bind ?p ?f =>
      let run1 := fresh "run" in
      let run2 := fresh "run" in
      let x := fresh "x" in
      let ω := fresh "ω" in
      let hbind := fresh "hbind" in
      pose proof (FreerDPS.HoareFacts.to_hoare_post_bind_assoc c p f hrun) as hbind;
      destruct hbind as [x [ω [run1 run2]]];
      clear hrun

    | ?a => idtac
    end

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (request_then ?e ?f)) ?ω ?x ?ω' =>
    cleanvert hrun;
    lazymatch goal with
    | next : exists _, post _ _ _ _ /\ _ |- _ =>
      let ω'' := fresh "ω" in
      let o_callee := fresh "o_callee" in
      let run := fresh "run" in
      destruct next as [ω'' [o_callee run]]
    | _ => idtac
    end

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (local ?y)) ?ω ?x ?ω' =>
    cleanvert hrun

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (Ret ?y)) ?ω ?x ?ω' =>
    cleanvert hrun

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (when ?b ?p)) ?ω ?x ?ω' =>
    unfold when in hrun;
    unroll_post_core hrun

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (impure_bind (local ?y) ?f)) ?ω ?x ?ω' =>
    change (post (lifter (i:=ifce) (M:=m) (interface_to_hoare c) (A:=_) (f y)) ω x ω') in hrun;
    cbn beta in hrun;
    unroll_post_core hrun

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (match ?b with true => ?p | false => ?q end)) ?ω ?x ?ω' =>
    let equ := fresh "equ" in
    destruct b eqn:equ

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (impure_bind ?p ?f)) ?ω ?x ?ω' =>
    let run1 := fresh "run" in
    let run2 := fresh "run" in
    let y := fresh "x" in
    let ω0 := fresh "ω" in
    let hbind := fresh "hbind" in
    pose proof (FreerDPS.HoareFacts.to_hoare_post_bind_assoc c p f hrun) as hbind;
    destruct hbind as [y [ω0 [run1 run2]]];
    clear hrun

  | post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (bind ?p ?f)) ?ω ?x ?ω' =>
    let run1 := fresh "run" in
    let run2 := fresh "run" in
    let y := fresh "x" in
    let ω0 := fresh "ω" in
    let hbind := fresh "hbind" in
    pose proof (FreerDPS.HoareFacts.to_hoare_post_bind_assoc c p f hrun) as hbind;
    destruct hbind as [y [ω0 [run1 run2]]];
    clear hrun

  | post (bind ?p ?f) ?ω ?x ?ω' =>
    let run1 := fresh "run" in
    let run2 := fresh "run" in
    let y := fresh "x" in
    let ω0 := fresh "ω" in
    destruct hrun as [y [ω0 [run1 run2]]]

  | ?a => idtac
  end.

Ltac easy_simpl hyp := cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
] in *; try unfold when in *; try unfold skip in *; simplify_gens; repeat destruct_if_when_in hyp.

(*
  Disabled for now: this newer recursive "unroll everything" pass changed the
  proof-state shape and broke older proof scripts that rely on predictable
  generated names such as [run], [run0], and [o_callee].

Ltac unroll_post_all :=
  repeat multimatch goal with
         | H : post (interface_to_hoare ?c (A:=_) ?e) ?ω ?x ?ω' |- _ =>
             let o_callee := fresh "o_callee" in
             let equ := fresh "equ" in
             destruct H as [o_callee equ];
             subst;
             simplify_gens
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (local ?y)) ?ω ?x ?ω' |- _ =>
             cleanvert H
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (Ret ?y)) ?ω ?x ?ω' |- _ =>
             cleanvert H
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (request_then ?e ?f)) ?ω ?x ?ω' |- _ =>
             cleanvert H;
             match goal with
             | next : exists _, post _ _ _ _ /\ _ |- _ =>
                 let ω'' := fresh "ω" in
                 let o_callee := fresh "o_callee" in
                 let run := fresh "run" in
                 destruct next as [ω'' [o_callee run]]
             end
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (when ?b ?p)) ?ω ?x ?ω' |- _ =>
             unfold when in H;
             unroll_post_all
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (impure_bind (local ?y) ?f)) ?ω ?x ?ω' |- _ =>
             change (post (lifter (i:=ifce) (M:=m) (interface_to_hoare c) (A:=_) (f y)) ω x ω') in H
             ; cbn beta in H
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (match ?b with true => ?p | false => ?q end)) ?ω ?x ?ω' |- _ =>
             let equ := fresh "equ" in
             destruct b eqn:equ;
             unroll_post_all
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (impure_bind ?p ?f)) ?ω ?x ?ω' |- _ =>
             let run1 := fresh "run" in
             let run2 := fresh "run" in
             let y := fresh "x" in
             let ω0 := fresh "ω" in
             let hbind := fresh "hbind" in
             pose proof (FreerDPS.HoareFacts.to_hoare_post_bind_assoc c p f H) as hbind;
             destruct hbind as [y [ω0 [run1 run2]]];
             clear H
         | H : post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) ?p) ?ω ?x ?ω' |- _ =>
             let p' := (eval hnf in p) in
             tryif constr_eq p p'
             then fail 1
             else change (post (lifter (i:=ifce) (M:=m) (interface_to_hoare c) (A:=_) p') ω x ω') in H
         | H : post (bind ?p ?f) ?ω ?x ?ω' |- _ =>
             let run1 := fresh "run" in
             let run2 := fresh "run" in
             let y := fresh "x" in
             let ω0 := fresh "ω" in
             destruct H as [y [ω0 [run1 run2]]]
         end.
*)

Tactic Notation "unroll_post" hyp(run) := unroll_post_core run.
Tactic Notation "run_simpl" hyp(run) := unroll_post_core run.
