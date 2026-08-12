From mathcomp Require Import all_boot all_order all_algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Init effect freer free_choice common_ping.

Local Open Scope nat_scope.
Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope freer_flip_scope.

Section lossy_round_trip.
Import FreerFlipDenote.
Context {R : realType} {M : choiceEqFreerMonad R}.
Implicit Types (m : msg) (psucc : {prob R}).

Definition transmit psucc m : M (option msg) :=
  Ret (Some m) <|| psucc ||> Ret None.

Lemma transmit1 m : transmit 1%:i01 m ≈ Ret (Some m).
Proof. exact: freer_choice1. Qed.

Lemma ping_pong1 : ping_pong (transmit:=transmit) 1%:i01 ≈ Ret GotPong.
Proof.
rewrite /ping_pong /client_send /server_reply /client_receive.
by rewrite transmit1 bindretf transmit1 bindretf.
Qed.

Lemma ping_pongs1 fuel : ping_pongs (transmit:=transmit) 1%:i01 fuel ≈ Ret GotPong.
Proof.
by elim : fuel => [|n IH];
    rewrite ping_pongsE ping_pong1 ?bindretf.
Qed.

Lemma ping_pong_distribution psucc :
  ping_pong (transmit:=transmit) psucc ≈ exchange_once (choose:=freer_choice) psucc.
Proof.
rewrite /ping_pongs /ping_pong.
by repeat rewrite freer_choice_bindDl !bindretf.
Qed.

Lemma ping_pongs_exchanges psucc fuel :
  ping_pongs (transmit:=transmit) psucc fuel ≈ exchanges (choose:=freer_choice) psucc fuel.
Proof.
elim: fuel => [|fuel IH].
  exact: ping_pong_distribution.
rewrite ping_pongsSE ping_pong_distribution exchangesSE.
by rewrite !freer_choice_bindDl !bindretf IH.
Qed.

Lemma freer_choice0 (A : UU0) (a b : M A) :
  a <|| 0%:i01 ||> b ≈ b.
Proof.
have cplt0 : ((0%:i01 : {prob R})%:num.~%:i01) = 1%:i01.
  by exact/val_inj/GRing.subr0.
by rewrite freer_choiceC cplt0 freer_choice1.
Qed.

Lemma freer_flip_choice psucc :
  @wBisim M _ (Ret true <|| psucc ||> Ret false) (flip psucc).
Proof.
rewrite /freer_choice -[X in _ ≈ X]bindmret.
by apply: bindfwB=> -[].
Qed.

Lemma ping_pong_success_probability psucc :
  ping_pong_success (transmit:=transmit) (psucc%:num.~%:i01) ≈
    flip (p_ex_once (psucc%:num.~%:i01)).
Proof.
  rewrite ping_pong_successE success_ofE ping_pong_distribution.
  rewrite /exchange_once /exchange p_ex_onceE.
  rewrite !freer_choice_bindDl !bindretf !success_eventE -freer_flip_choice.

  set d := psucc%:num.~%:i01.
  have [->/=|d0] := eqVneq d 0%:i01.
  - by rewrite p_of_0s !freer_choice0.
  have [->/=|d1] := eqVneq d 1%:i01.
  - by rewrite p_of_1s !freer_choice1.
  have p1 : [p_of d, d] != 1%:i01.
    by rewrite p_of_rs1 (negbTE d1) andbF.
  (* Give RHS the same form as LHS *)
  rewrite -[X in _ ≈ _ <|| _ ||> X]
    (freer_choicemm _ [q_of d, d] (Ret false)).
  by rewrite freer_choiceA (s_of_pqK p1) (r_of_pqK p1 d0).
Qed.


Lemma ping_pongs_success_stepE psucc fuel :
  ping_pongs_success (transmit:=transmit) psucc (fuel.+1) ≈
    (Ret true <|| psucc ||> ping_pongs_success (transmit:=transmit) psucc fuel) <|| psucc ||>
    ping_pongs_success (transmit:=transmit) psucc fuel.
Proof.
  rewrite ping_pongs_successE success_ofE ping_pongsE /ping_pong.
  rewrite !freer_choice_bindDl !bindretf 2!bindA !freer_choice_bindDl !bindretf.
  by rewrite success_eventE.
Qed.

Theorem ping_pong_retry_success_probability psucc (fuel : nat) :
    ping_pongs_success (transmit:=transmit) (psucc%:num.~%:i01) fuel ≈
      flip (p_exs (psucc%:num.~%:i01) fuel).
  Proof.
    elim : fuel => [|n].
    - exact: ping_pong_success_probability.
rewrite ping_pongs_success_stepE !p_exsE p_exE p_ex_onceE=> ->.
    set d := psucc%:num.~%:i01.


    have [->/=|d0] := eqVneq d 0%:i01.
    - by rewrite -!freer_flip_choice p_of_0s s_of_0q freer_choice0.
    have [->/=|d1] := eqVneq d 1%:i01.
    - by rewrite -!freer_flip_choice p_of_1s s_of_1q !freer_choice1.

    rewrite -p_exsE.
    have p1 : [p_of d, d] != 1%:i01 by rewrite p_of_rs1 (negbTE d1) andbF.

  (* rewrite -[X in _ ≈ _ <|| _ ||> (flip (p_exs d n))] *)
    (* (freer_choicemm _ [q_of d, d] (Ret false)). *)
    (* rewrite -[flip (p_exs d n) in RHS](choicemm [q_of d, d]). *)
    (* by rewrite freer_choiceA (s_of_pqK p1) (r_of_pqK p1 d0). *)
  Admitted.

End lossy_round_trip.
