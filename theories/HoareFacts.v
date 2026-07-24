(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

Attributes deprecated(
  note="The contents of this file will be moved to `Hoare.v`.").

From FreerDPS Require Import Init Effect Freer Contract Hoare.
Generalizable All Variables.

(** * General Lemmas *)

Lemma to_hoare_step `{MayProvide Fx F} `(c : contract F Ω)
   `(e : Fx a) `(f : a -> freer Fx a)
   `(hpre : pre
      (to_hoare (im:=freer Fx) c (impure e f)) ω)
    (x : a) (step : gen_callee_obligation c ω e x)
  : pre
      (to_hoare (im:=freer Fx) c (f x))
      (gen_witness_update c ω e x).

Proof.
  destruct hpre as [hbefore hafter].
  apply hafter.
  cbn.
  unfold gen_callee_obligation, gen_witness_update in *.
  now destruct proj_p.
Qed.

#[global] Hint Resolve to_hoare_step : freespec.

Lemma to_hoare_pre_bind_assoc `{MayProvide Fx F} `(c : contract F Ω)
   `(p : freer Fx a)
   `(Hp : pre
      (to_hoare (im:=freer Fx) c p) ω)
   `(f : a -> freer Fx b)
    (run : forall (x : a) (ω' : Ω),
      post
        (to_hoare (im:=freer Fx) c p)
        ω x ω' ->
      pre
        (to_hoare (im:=freer Fx) c (f x)) ω')
  : pre
      (to_hoare (im:=freer Fx) c (freer_bind p f)) ω.

Proof.
  revert ω Hp run.
  induction p; intros ω Hp run.
  + now apply run.
  + cbn in Hp.
    destruct Hp as [He Hn].
    split.
    ++ exact He.
    ++ intros x ω' Hpost.
       specialize Hn with x ω'.
       destruct Hpost.
       rewrite -> H2 in *.
       assert (Hpre : pre
          (to_hoare (im:=freer Fx) c (f0 x))
          (gen_witness_update c ω op x))
         by now apply Hn.
       apply H0; [ apply Hpre |].
       intros y ω'' Hpost.
       apply run.
       cbn.
       exists x.
       exists ω'.
       split; [split |].
       +++ exact H1.
       +++ exact H2.
       +++ rewrite H2.
           exact Hpost.
Qed.

Lemma to_hoare_post_bind_assoc `{MayProvide Fx F} `(c : contract F Ω)
   `(p : freer Fx a) `(f : a -> freer Fx b)
   `(Hp : post
      (to_hoare (im:=freer Fx) c (freer_bind p f)) ω x ω')
  : exists y ω'',
    post
      (to_hoare (im:=freer Fx) c p) ω y ω'' /\
    post
      (to_hoare (im:=freer Fx) c $ f y) ω'' x ω'.

Proof.
move: ω Hp; elim p=>[in_a|Y op k IH] ω.
- by exists in_a, ω.
case=>y [ω'' [Hp1 ]].
move:IH=>/[apply].
move=> [z [ω''' [Hp2 Hp3]]].
exists z, ω'''.
split=>//.
exists y, ω''.
by split.
Qed.

Lemma to_hoare_contractprod `{Provide Fx F, Provide Fx E}
   `(ci : contract F ΩF) `(cj : contract E ΩE)
   `(p : freer Fx a)
   `(prei : pre
      (to_hoare (im:=freer Fx) ci p) ωF)
   `(prej : pre
      (to_hoare (im:=freer Fx) cj p) ωE)
  : pre
      (to_hoare (im:=freer Fx) (ci * cj) p) (ωF, ωE).

Proof.
  revert ωF prei ωE prej.
  induction p; intros ωF prei ωE prej.
  + auto.
  + destruct prei as [calleri Hcalleei].
    destruct prej as [callerj Hcalleej].
    split.
    ++ now split.
    ++ intros x [ωF' ωE'] [[calleei calleej] equωs].
       cbn in equωs.
       inversion equωs; subst.
       apply H3.
       +++ apply Hcalleei.
           now split.
       +++ apply Hcalleej.
           now split.
Qed.

#[global] Hint Resolve to_hoare_contractprod : freespec.

Lemma contract_equ_pre `(c1 : contract F Ω1) `(c2 : contract F Ω2)
   `(equ : contract_equ c1 c2) (ω1 : Ω1)
   `(p : freer F A)
  : pre
      (to_hoare (im:=freer F) c1 p) ω1 <->
    pre
      (to_hoare (im:=freer F) c2 p) (contract_iso_lr equ ω1).

Proof.
  elim: equ => f g iso1 iso2 caller_equ callee_equ witness_equ.
  move: ω1.
  elim: p=> [a | B e k IH] ω1. 
  - by split.
  rewrite /=/gen_caller_obligation/gen_callee_obligation/gen_witness_update/=.
  rewrite (caller_equ ω1 B e).
  setoid_rewrite (callee_equ ω1 B e).
  split => [[ocaller onext] | [ocaller onext]];
  split => // x ω1' [ocallee owitness].
  - by rewrite owitness -witness_equ -IH; eauto.
  rewrite IH; eauto.
  rewrite owitness /= witness_equ; eauto.
Qed.

#[global] Hint Resolve contract_equ_pre : freespec.

Lemma contract_equ_post `(c1 : contract F Ω1) `(c2 : contract F Ω2)
   `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1)
   `(p : freer F a) (x : a)
    (post1 : post
      (to_hoare (im:=freer F) c1 p) ω1 x ω1')
  : post
      (to_hoare (im:=freer F) c2 p)
      (contract_iso_lr equ ω1) x (contract_iso_lr equ ω1').

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
