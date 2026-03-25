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
  | |- context[when (negb ?B) _] => case_eq B; intros equ_cond; cbn
  | |- context[when ?B _] => case_eq B; intros equ_cond; cbn
  | |- context[if (negb ?B) then _ else _] => case_eq B; intros equ_cond; cbn
  | |- context[if ?B then _ else _] => case_eq B; intros equ_cond; cbn
  | _ => idtac
  end.

Ltac destruct_if_when_in hyp :=
  let equ_cond := fresh "equ" in
  match type of hyp with
  | context[when (negb ?B) _] => case_eq B;
                                 intro equ_cond;
                                 rewrite equ_cond in hyp
  | context[when ?B _] => case_eq B;
                          intro equ_cond;
                          rewrite equ_cond in hyp
  | context[if (negb ?B) then _ else _] => case_eq B;
                                           intro equ_cond;
                                           rewrite equ_cond in hyp
  | context[if ?B then _ else _] => case_eq B;
                                    intro equ_cond;
                                    rewrite equ_cond in hyp
  | _ => idtac
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
Ltac prove_impure :=
  idtac "pr;imp"; repeat (cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
              lifter
          ] in *;
          simplify_gens;
          destruct_if_when);
  lazymatch goal with

  | |- _ /\ _ =>
    split;
    prove_impure

  | |- forall _ _, _ /\ _ = _ -> _ =>
    let x := fresh "x" in
    let ω' := fresh "ω" in
    let o_caller := fresh "o_caller" in
    let equ := fresh "equ" in
    intros x ω' [o_caller equ];
    repeat rewrite -> equ in *; clear equ; clear ω';
    prove_impure

    | |- pre ?pcond ?ω =>

    lazymatch pcond with 
      | lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) ?p => let p := (eval hnf in p) in
        lazymatch p with
        | request_then ?e ?f =>
          let o_caller := fresh "o_caller" in
          assert (o_caller : gen_caller_obligation c ω e) ; 
          [ prove_impure | constructor; prove_impure]
        | local _ => constructor
        | impure_bind (impure_bind ?p ?f) ?g =>
          rewrite (bindA p f g);
          prove_impure
        | bind ?p ?f =>
          apply to_hoare_pre_bind_assoc; [ eauto with freespec
                                        | let x := fresh "x" in
                                          let ω' := fresh "ω" in
                                          let hpost := fresh "hpost" in
                                          intros x ω' hpost;
                                          prove_impure
                                        ]
        | _ => eauto with freespec
        end

    | to_hoare ?c ?p => let p := (eval hnf in p) in
      lazymatch p with
      | request_then ?e ?f =>
        let o_caller := fresh "o_caller" in
        assert (o_caller : gen_caller_obligation c ω e) ; 
        [ prove_impure | constructor; prove_impure]
      | local _ => constructor
      | impure_bind (impure_bind ?p ?f) ?g =>
        rewrite (bindA p f g);
        prove_impure
      | bind ?p ?f =>
        apply to_hoare_pre_bind_assoc; [ eauto with freespec
                                      | let x := fresh "x" in
                                        let ω' := fresh "ω" in
                                        let hpost := fresh "hpost" in
                                        intros x ω' hpost;
                                        prove_impure
                                      ]
      | _ => eauto with freespec
      end
    | _ => idtac "==>not handled"
    end 
  | |- ?a =>
    eauto with freespec

  end.

Tactic Notation "prove" "impure" := prove_impure.
Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.

Ltac unroll_post run :=
  repeat (cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
          ] in *;
          simplify_gens;
          destruct_if_when_in run);
  lazymatch type of run with

  | post (to_hoare ?c ?p) ?ω ?x ?ω' =>
    let p := (eval hnf in p) in
    lazymatch p with
    | request_then ?e ?f =>
      inversion run; ssubst;
      clear run;
      lazymatch goal with
      | next : exists _, post (interface_to_hoare c _ e) _ _ _ /\ _ |- _ =>
        let ω'' := fresh "ω" in
        let o_callee := fresh "o_callee" in
        let run := fresh "run" in
        destruct next as [ω'' [o_callee run]];
        unroll_post run
      | _ => idtac
      end

    | local ?x =>
      inversion run; ssubst;
      clear run

    | bind ?p ?f =>
      apply (bindA c p f) in run;
      let run1 := fresh "run" in
      let run2 := fresh "run" in
      let x := fresh "x" in
      let ω := fresh "ω" in
      destruct run as [x [ω [run1 run2]]];
      unroll_post run1; unroll_post run2

    | ?a => idtac
    end

  | ?a => idtac
  end.

  Ltac cleanvert hyp := inversion hyp; ssubst; move:hyp=>_.

Ltac easy_simpl hyp := idtac "--simpl"; do ? [cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
] in *; simplify_gens; do ? destruct_if_when_in hyp].

Ltac run_simpl run := 
  idtac "run_simpl: " run;
  easy_simpl run ;
  match type of run with
| post (to_hoare ?c ?p) ?ω ?x ?ω' => 
  idtac "=> to_hoare" "c: " c " ; p: " p;
  let p := (eval hnf in p) in
  idtac "=> hnf of p: " p;
  match p with
  | request_then ?e ?f =>
    idtac "=> => impure!";
    cleanvert run;
    idtac "=> => inverted";
    match goal with
    | next : exists _, post (interface_to_hoare c (A:=_) e) _ _ _ /\ _ |- _ => 
        idtac "=> => => found next: " next;
        let ω'' := fresh "ω" in 
        let o_callee := fresh "o_callee" in 
        let run := fresh "run" in
        case: next =>ω'' [o_callee run];
        idtac "=> => => destructed as : [" ω'' "[" o_callee ", " run"]]";
        run_simpl run; 
        idtac "<== <== after run"
    | _ => idtac "<== branched out exists match"
    end
  | local ?x => idtac "=> => PURE!"; cleanvert run
  | _ => idtac "<== freer out" 
  end
| post (lifter (i:=?ifce) (M:=?m) (interface_to_hoare ?c) (A:=_) (bind ?f ?g)) _ _ _  =>  
      idtac "=> lifter bind";
      let run1 := fresh "lrun" in
      let run2 := fresh "rrun" in
      let ω := fresh "ω" in 
      let x := fresh "x" in 
      idtac "=> var names : " run1 run2 ω x;
      move: run => /(to_hoare_post_bind_assoc c f g);
      idtac "=> thpba applied"; 
      move => [x [ω [run1 run2]]]; 
      idtac "=> destructed run";
      idtac "=>> run first:";
      run_simpl run1; 
      idtac "<<= finished first";
      idtac "=>> run second:";
      run_simpl run2;
      idtac "<<= finished second"
      (* idtac *)
      (* destruct run as [x [ω [run1 run2]]]; *)
      (* run_simpl run1; run_simpl run2 *)
| ?a => idtac "not post"
end.