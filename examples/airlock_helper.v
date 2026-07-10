(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

From FreerDPS Require Import Init Core Freer Hoare HoareFacts.
From mathcomp Require Import all_boot.

Generalizable All Variables.

Import FreerFuns.

Module for_hoare_m.

Lemma to_hoare_distinguished_request_preI
    {Fx F G : effect}
    `{MayProvide Fx F, Provide Fx G, Distinguish Fx G F}
    {im : freerMonad Fx} `(c : contract F Ω)
    {A} (op : G A) (ω : Ω) :
  pre (to_hoare (im:=im) c
    (trigger (Fx:=Fx) (F:=G) (im:=im)
      (inj_p (Fx:=Fx) op))) ω.
Proof.
by rewrite to_hoare_requestE /hoare_of_contract
  /gen_caller_obligation (@distinguish Fx G F).
Qed.

Lemma to_hoare_distinguished_request_postE
    {Fx F G : effect}
    `{MayProvide Fx F, Provide Fx G, Distinguish Fx G F}
    {im : freerMonad Fx} `(c : contract F Ω)
    {A} (op : G A) (ω : Ω) (x : A) (ω' : Ω) :
  post (to_hoare (im:=im) c
    (trigger (Fx:=Fx) (F:=G) (im:=im)
      (inj_p (Fx:=Fx) op))) ω x ω' <->
  ω' = ω.
Proof.
by rewrite to_hoare_requestE /=
  /gen_witness_update /gen_callee_obligation
  (@distinguish Fx G F);
   split=> [[-> _] | ->].
Qed.

Lemma denote_skipE
    `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω) :
  denote (hoare Ω) (hoare_of_contract c) unit
    (skip : im unit) = Ret tt.
Proof. exact: denote_ret. Qed.

Lemma to_hoare_skip_preI
    `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω) (ω : Ω) :
  pre (to_hoare (im:=im) c (skip : im unit)) ω.
Proof. by rewrite /to_hoare denote_skipE. Qed.

Lemma to_hoare_when_preE
    `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω) {A} (guard : bool) (p : im A) (ω : Ω) :
  pre (to_hoare (im:=im) c (when guard p)) ω <->
  if guard then pre (to_hoare (im:=im) c p) ω else True.
Proof.
by case: guard=> /=;
  [rewrite to_hoare_bind_preE; split=> [[ ] | ] //|];
  split=> // *; exact: to_hoare_skip_preI.
Qed.

Lemma to_hoare_when_postE
    `{MayProvide Fx F} {im : freerMonad Fx}
    `(c : contract F Ω) {A} (guard : bool) (p : im A)
    (ω : Ω) (x : unit) (ω' : Ω) :
  post (to_hoare (im:=im) c (when guard p)) ω x ω' <->
  if guard
  then exists y, post (to_hoare (im:=im) c p) ω y ω'
  else ω' = ω.
Proof.
case: x; case: guard=> /=;
  rewrite ?to_hoare_bind_postE /to_hoare denote_skipE;
  last first.
- by split=> [[_ ->] | <-].
by split=> [[y [? [? [_ <-]]]] | [y ?]];
  exists y=>//;
  exists ω'; split.
Qed.

End for_hoare_m.

Module for_freer_m.

Lemma denote_when_request (Fx : effect) (M : freerMonad Fx) (N : monad)
    (l : Fx ~~> N) (A X : Type) (guard : A -> bool) (op : Fx X) :
  denote N l unit \o
      (fun x => when (guard x) (request X op : M X)) =
    fun x =>
      if guard x then
        l X op >>= (denote N l unit \o fun=> (skip : M unit))
      else denote N l unit (skip : M unit).
Proof.
by apply/funext=> x; rewrite compE denote_if;
  case: (guard x)=> //=;
  rewrite denote_bind denote_request.
Qed.

End for_freer_m.

Module for_component_m.

Definition correct_component `{MayProvide Ex E} {im : freerMonad Ex}
    `(c : component F Ex) `(cF : contract F ΩF)
    `(cE : contract E ΩE) (pred : ΩF -> ΩE -> Prop) :
  Prop :=
  forall (ωF : ΩF) (ωE : ΩE) (init : pred ωF ωE)
      `(op : F α) (o_caller : caller_obligation cF ωF op),
    pre (to_hoare cE $ c α op) ωE /\
    forall (x : α) (ωE' : ΩE),
      post (to_hoare (im:=im) cE (c α op)) ωE x ωE' ->
      callee_obligation cF ωF op x /\
      pred (witness_update cF ωF op x) ωE'.

End for_component_m.

Export for_freer_m for_hoare_m for_component_m.
