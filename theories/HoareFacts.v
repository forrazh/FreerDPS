(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreerDPS Require Import Interface Impure Contract Hoare.
From monae Require Import preamble hierarchy.
Generalizable All Variables.

(** * General Lemmas *)

Lemma to_hoare_step `{MayProvide ix i} `(c : contract i Ω)
   `(e : ix a) `(f : a -> impure ix a)
   `(hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (request_then e f)) ω)
    (x : a) (step : gen_callee_obligation c ω e x)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) c (f x)) (gen_witness_update c ω e x).

Proof.
  destruct hpre as [hbefore hafter].
  apply hafter.
  cbn.
  unfold gen_callee_obligation, gen_witness_update in *.
  now destruct proj_p.
Qed.

#[global] Hint Resolve to_hoare_step : freespec.

Lemma to_hoare_contractprod `{Provide ix i, Provide ix j}
   `(ci : contract i Ωi) `(cj : contract j Ωj)
   `(p : impure ix a)
   `(prei : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) ci p) ωi) `(prej : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) cj p) ωj)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (ci * cj) p) (ωi, ωj).

Proof.
  revert ωi prei ωj prej.
  induction p; intros ωi prei ωj prej.
  + auto.
  + destruct prei as [calleri Hcalleei].
    destruct prej as [callerj Hcalleej].
    split.
    ++ now split.
    ++ intros x [ωi' ωj'] [[calleei calleej] equωs].
       cbn in equωs.
       inversion equωs; subst.
       apply H3.
       +++ apply Hcalleei.
           now split.
       +++ apply Hcalleej.
           now split.
Qed.

#[global] Hint Resolve to_hoare_contractprod : freespec.

Lemma contract_equ_pre `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : contract_equ c1 c2) (ω1 : Ω1)
   `(p : impure i a)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c1 p) ω1 <-> pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c2 p) (contract_iso_lr equ ω1).

Proof.
  induction equ.
  revert ω1.
  induction p; intros ω1.
  + now split.
  + cbn.
    split.
    ++ intros [ocaller onext].
       split; auto.
       * apply caller_equ. apply ocaller.

       intros x ω1' [ocallee owitness].
       rewrite owitness. cbn in H. unfold gen_witness_update.
       induction (proj_p e).
        -- rewrite <-witness_equ.
          rewrite <- H; auto.
          admit.
        -- rewrite <- H. admit. 
    ++ intros [ocaller onext].
       split; auto.
       * apply caller_equ. apply ocaller.

       intros x ω1' [ocallee owitness].
       apply H; eauto.
       rewrite owitness.
       cbn.
       rewrite witness_equ.
       eauto.
       admit.
Admitted.

#[global] Hint Resolve contract_equ_pre : freespec.

Lemma contract_equ_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1)
   `(p : impure i a) (x : a)
    (post1 : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c1 p) ω1 x ω1')
  : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure i) c2 p) (contract_iso_lr equ ω1) x (contract_iso_lr equ  ω1').

Proof.
  induction equ.
  cbn in *.
  revert x ω1 ω1' post1.
  induction p; intros y ω1 ω1' post1.
  + destruct post1 as [xequ ω1equ].
    cbn.
    now subst.
  + cbn in post1.
    destruct post1 as [x [ω1'' [[ocallee owitness] post1]]].
    eapply H in post1.
    exists x.
    exists (f ω1'').
    split; auto.
    cbn.
    repeat split.
    ++ eapply callee_equ; eauto.
    ++ rewrite owitness.
       apply witness_equ.
Qed.

#[global] Hint Resolve contract_equ_post : freespec.
