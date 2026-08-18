From mathcomp Require Import all_boot all_order all_algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv.

Local Open Scope nat_scope.
Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
(* Local Open Scope freer_flip_scope. *)
(* Import FreerFlipDenote. *)


Inductive lossy_channel_api (R : realType) : effect :=
| TRANSMIT :
    {prob R} -> msg -> lossy_channel_api R (option msg).

Section lossy_contract.
Context {R : realType} {Fx : effect} `{lossy_channel_api R -< Fx}
  {M : freerMonad Fx}.
Implicit Types (q : seq msg) (psucc : {prob R}) (m : msg).

Definition may_append q (r : option msg) :=
  if r is Some m then rcons q m else q.

Definition lossy_step q :
    forall X, lossy_channel_api R X -> X -> seq msg :=
  fun X operation result =>
    match operation in lossy_channel_api _ X return X -> seq msg with
    | TRANSMIT _ m => may_append q
    end result.

Definition lossy_o_caller q :
    forall X, lossy_channel_api R X -> Prop :=
  fun X op => True.

Definition lossy_o_callee q :
    forall X, lossy_channel_api R X -> X -> Prop :=
  fun X op =>
    match op in lossy_channel_api _ X return X -> Prop with
    | TRANSMIT _ message => fun result =>
        result = Some message \/ result = None
    end.

Definition lossy_contract : contract (lossy_channel_api R) (seq msg) :=
  make_contract lossy_step lossy_o_caller lossy_o_callee.

Definition transmit psucc m :
    M (option msg) :=
  ptrigger (@TRANSMIT R psucc m).

Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma transmit_respect psucc m (q : seq msg) :
  pre (lossy_contract ||> transmit psucc m) q.
Proof. by rewrite to_hoare_ptrigger_preE. Qed.

Definition channel_growth q q' : Prop := ((size q) <= size q')%nat.

(* Successful run adds a value in the q, while failed one doesn't. *)
Lemma transmit_run psucc m q r q' :
  post (lossy_contract ||> transmit psucc m) q r q' -> channel_growth q q'.
Proof.
move/to_hoare_ptrigger_postE=> /= [->].
case=> ->.
- by rewrite /channel_growth size_rcons.
- by rewrite /channel_growth.
Qed.

End lossy_contract.

Section lossy_channel.
Context {R : realType} {Fx : effect}
  `{StrictProvide2 Fx (@FlipEff R) (STORE (seq msg))}
  {M : choiceEqFreerMonad R Fx _}.
Implicit Types (psucc : {prob R}) (m : msg).

Definition transmitter psucc m :
    M (option msg) :=
  (iget >>= fun q =>
    iput (rcons q m) >>
    Ret (Some m)) <|| psucc ||> Ret None.

Definition lossy_channel :
    component (M := M) (@lossy_channel_api R) Fx :=
  fun X op =>
    match op in lossy_channel_api _ X return M X with
    | TRANSMIT psucc m => transmitter psucc m
    end.

Lemma channel_pre psucc m q :
  pre ((store_specs (seq msg)) |> (lossy_channel _ (@TRANSMIT R psucc m))) q.
Proof.
apply: th_pre_bindA;
  first by exact: to_hoare_distinguished_trigger_preI.
move=> [] q_flip /to_hoare_distinguished_trigger_postE ->;
    last by exact: to_hoare_ret_preI.
by do 2 (apply: th_pre_bindA=>*;
  first by rewrite to_hoare_ptrigger_preE);
  exact: to_hoare_ret_preI.
Qed.

Lemma channel_post psucc m q_abstract q_concrete result q_concrete' :
  channel_growth q_abstract q_concrete ->
  post (store_specs (seq msg) |> transmitter psucc m)
    q_concrete result q_concrete' ->
  (result = Some m \/ result = None) /\
  channel_growth (may_append q_abstract result) q_concrete'.
Proof.
move=> growth.
rewrite th_post_bindA=> -[success [?[ ]]].
rewrite to_hoare_distinguished_trigger_postE=> ->.
case: success;
  (* Message dropped *)
  last by move/to_hoare_ret_postE=> [<- <-];
    split=> //; right.
(* Message passed *)
(* Can the following lemmas be simplified somehow ? *)
rewrite th_post_bindA=> -[? [? [+ +]]];
  rewrite to_hoare_ptrigger_postE /= => -[-> <-];
  rewrite th_post_bindA=> -[? [? [+ +]]];
  rewrite to_hoare_ptrigger_postE=> -[-> _];
  rewrite to_hoare_ret_postE=> -[<- <-].
split; first by left.
rewrite /channel_growth !size_rcons.
exact: growth.
Qed.

Theorem channel_correct :
  correct_component lossy_channel (M := M)
    lossy_contract (store_specs (seq msg)) channel_growth.
Proof.
move=> q_abstract q_concrete growth X [psucc m] _; split=>[|?? run].
- exact: channel_pre.
- exact/channel_post/run/growth.
Qed.

End lossy_channel.
