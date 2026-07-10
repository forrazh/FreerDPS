(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* From ExtLib Require Import Monad. *)
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Init Interface Contract Impure Hoare HoareFacts.

(** Legacy compatibility tactics.

    This module is intentionally not exported by [Core].  New proofs should
    use the named views and reasoning lemmas from [Hoare] and [HoareFacts]
    directly. *)

#[local] Ltac destruct_if_when :=
  let equ_cond := fresh "equ_cond" in
  match goal with
  | |- context[when (negb ?B) _] => case_eq B; intros equ_cond; cbn
  | |- context[when ?B _] => case_eq B; intros equ_cond; cbn
  | |- context[if (negb ?B) then _ else _] => case_eq B; intros equ_cond; cbn
  | |- context[if ?B then _ else _] => case_eq B; intros equ_cond; cbn
  | _ => idtac
  end.

#[local] Ltac simplify_gens :=
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

#[local] Ltac legacy_prepare_impure :=
  repeat (cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
              lifter
          ] in *;
          simplify_gens;
          destruct_if_when).

#[local] Ltac prove_impure :=
  legacy_prepare_impure;
  let prove_program c p ω :=
    let p := (eval hnf in p) in
    lazymatch p with
    | request_then ?e ?f =>
        let o_caller := fresh "o_caller" in
        assert (o_caller : gen_caller_obligation c ω e);
        [ prove_impure
        | apply to_hoare_request_then_preI;
          [ exact o_caller
          | let x := fresh "x" in
            let o_callee := fresh "o_callee" in
            intros x o_callee; prove_impure ] ]
    | local _ => apply to_hoare_local_preI
    | impure_bind (impure_bind ?p ?f) ?g =>
        rewrite (bindA p f g); prove_impure
    | bind ?p ?f =>
        apply to_hoare_pre_bind_assoc;
        [ eauto with freespec | intros; prove_impure ]
    | _ => eauto with freespec
    end in
  lazymatch goal with
  | |- _ /\ _ =>
      split; prove_impure
  | |- forall _ _, _ /\ _ = _ -> _ =>
      let x := fresh "x" in
      let ω' := fresh "ω" in
      let o_caller := fresh "o_caller" in
      let equ := fresh "equ" in
      intros x ω' [o_caller equ];
      rewrite -> equ in *; clear equ ω';
      prove_impure
  | |- pre ?pcond ?ω =>
      lazymatch pcond with
      | lifter (interface_to_hoare ?c) ?p => prove_program c p ω
      | to_hoare ?c ?p => prove_program c p ω
      | _ => eauto with freespec
      end
  | _ => eauto with freespec
  end.

Tactic Notation "prove" "impure" := prove_impure.
Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.
