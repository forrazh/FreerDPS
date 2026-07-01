(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

From mathcomp Require Import ssreflect.
From FreerDPS Require Import Interface Impure Contract Hoare.
From monae Require Import preamble hierarchy.

Generalizable All Variables.

(** * Weakest Preconditions *)

Definition wp {Σ α} (h : hoare Σ α) (Q : α -> Σ -> Prop) : Σ -> Prop :=
  fun σ =>
    pre h σ /\
    forall x σ', post h σ x σ' -> Q x σ'.

Definition wp_impure `{MayProvide ix i} {im : impureMonad ix} {Ω α}
    (c : contract i Ω) (p : im α) (Q : α -> Ω -> Prop) : Ω -> Prop :=
  wp (to_hoare c p) Q.

Lemma wp_intro {Σ α} (h : hoare Σ α) (Q : α -> Σ -> Prop) σ
    (Hpre : pre h σ)
    (Hpost : forall x σ', post h σ x σ' -> Q x σ') :
  wp h Q σ.
Proof. by split. Qed.

Lemma wp_pre {Σ α} (h : hoare Σ α) (Q : α -> Σ -> Prop) σ :
  wp h Q σ -> pre h σ.
Proof. by case. Qed.

Lemma wp_post {Σ α} (h : hoare Σ α) (Q : α -> Σ -> Prop) σ x σ' :
  wp h Q σ -> post h σ x σ' -> Q x σ'.
Proof. by case=>_ /[apply]. Qed.

Lemma wp_weaken {Σ α} (h : hoare Σ α) (Q Q' : α -> Σ -> Prop) σ :
  wp h Q σ ->
  (forall x σ', Q x σ' -> Q' x σ') ->
  wp h Q' σ.
Proof.
  move=>[Hpre Hpost] Hweaken.
  split.
  - exact: Hpre.
  move=>x σ' Hrun.
  exact: Hweaken (Hpost x σ' Hrun).
Qed.

Lemma wp_hoare_pure {Σ α} (x : α) (Q : α -> Σ -> Prop) σ :
  wp (hoare_pure x) Q σ <-> Q x σ.
Proof.
  split.
  - by case=>_ /(_ x σ); apply; split.
  move=>HQ; split=>// y σ' [<- <-].
  exact: HQ.
Qed.

Lemma wp_hoare_bind {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β)
    (Q : β -> Σ -> Prop) σ :
  wp (hoare_bind h k) Q σ <->
  wp h (fun x σ' => wp (k x) Q σ') σ.
Proof.
  split.
  - case=>[[Hpre Hnext] Hpost].
    split=>// x σ' Hrun.
    split.
    + exact: Hnext Hrun.
    move=>y σ'' Hk.
    apply: Hpost.
    by exists x, σ'.
  case=>Hpre Hpost.
  split.
  - split=>// x σ' /Hpost [].
    by [].
  move=>y σ'' [x [σ' [Hx Hk]]].
  move: (Hpost x σ' Hx)=>[_].
  exact.
Qed.

Lemma wp_ret {Σ α} (x : α) (Q : α -> Σ -> Prop) σ :
  wp (Ret x : hoare Σ α) Q σ <-> Q x σ.
Proof. exact: wp_hoare_pure. Qed.

Lemma wp_bind {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β)
    (Q : β -> Σ -> Prop) σ :
  wp (h >>= k) Q σ <->
  wp h (fun x σ' => wp (k x) Q σ') σ.
Proof. exact: wp_hoare_bind. Qed.

Lemma wp_interface `{H : MayProvide ix i} {Ω α} (c : contract i Ω)
    (e : ix α) (Q : α -> Ω -> Prop) ω :
  wp (@interface_to_hoare ix i H Ω c α e) Q ω <->
  gen_caller_obligation c ω e /\
  forall x, gen_callee_obligation c ω e x ->
       Q x (gen_witness_update c ω e x).
Proof.
  rewrite /wp /interface_to_hoare /=.
  split.
  - case=>Hcaller Hpost.
    split.
    + exact: Hcaller.
    move=>x Hcallee.
    apply: Hpost.
    by split.
  case=>Hcaller Hpost.
  split.
  - exact: Hcaller.
  move=>x ω' [Hcallee ->].
  exact: Hpost Hcallee.
Qed.

Lemma wp_impure_ret `{MayProvide ix i} {im : impureMonad ix} {Ω α}
    (c : contract i Ω) (x : α) (Q : α -> Ω -> Prop) ω :
  wp_impure c (Ret x : im α) Q ω <-> Q x ω.
Proof.
  rewrite /wp_impure /to_hoare impure_lift_ret.
  exact: wp_ret.
Qed.

Lemma wp_impure_bind `{MayProvide ix i} {im : impureMonad ix} {Ω α β}
    (c : contract i Ω) (p : im α) (k : α -> im β)
    (Q : β -> Ω -> Prop) ω :
  wp_impure c (p >>= k) Q ω <->
  wp_impure c p (fun x ω' => wp_impure c (k x) Q ω') ω.
Proof.
  rewrite /wp_impure /to_hoare impure_lift_bind.
  exact: wp_bind.
Qed.

Lemma wp_impure_request `{H : MayProvide ix i} {im : impureMonad ix} {Ω α}
    (c : contract i Ω) (e : ix α) (Q : α -> Ω -> Prop) ω :
  wp_impure c (request α e : im α) Q ω <->
  gen_caller_obligation c ω e /\
  forall x, gen_callee_obligation c ω e x ->
       Q x (gen_witness_update c ω e x).
Proof.
  rewrite /wp_impure /to_hoare impure_lift_request.
  exact: wp_interface.
Qed.

Lemma wp_impure_request_then `{MayProvide ix i} {Ω α β}
    (c : contract i Ω) (e : ix α) (k : α -> impure ix β)
    (Q : β -> Ω -> Prop) (ω : Ω) :
  wp_impure (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
    c (request_then e k) Q ω <->
  gen_caller_obligation c ω e /\
  forall x, gen_callee_obligation c ω e x ->
       wp_impure (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix)
         c (k x) Q (gen_witness_update c ω e x).
Proof.
  rewrite /wp_impure /to_hoare /wp /impure_lift /Impure.lifter /bind /=.
  split.
  - case=>[[Hcaller Hnext] Hpost].
    split.
    + exact: Hcaller.
    move=>x Hcallee.
    split.
    + apply: Hnext.
      by split.
    move=>y ω' Hk.
    apply: Hpost.
    exists x, (gen_witness_update c ω e x).
    by split=>//; split.
  case=>Hcaller Hnext.
  split.
  - split.
    + exact: Hcaller.
    move=>x ω' [Hcallee ->].
    by case: (Hnext x Hcallee).
  move=>y ω' [x [ω'' [[Hcallee ->] Hk]]].
  by case: (Hnext x Hcallee)=>_ /(_ y ω' Hk).
Qed.
