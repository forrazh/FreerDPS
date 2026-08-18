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

Lemma to_hoare_ptrigger_bind_postE {F' F} {Ω} `{F -< F'}
    {M' : freerMonad F'} {c : contract F Ω}
    {A B : Type} (op : F A) (f : A -> M' B)
    (ω : Ω) (y : B) (ω' : Ω) :
  post (to_hoare c (ptrigger op >>= f)) ω y ω' <->
  exists x,
    callee_obligation c ω op x /\
    post (to_hoare c (f x))
      (witness_update c ω op x) y ω'.
Proof.
rewrite th_post_bindA.
split.
- move=> [x [ω''
      [/to_hoare_ptrigger_postE [-> obligation] suffix]]].
  by exists x.
- move=> [x [obligation suffix]].
  exists x, (witness_update c ω op x); split=> //.
  by apply/to_hoare_ptrigger_postE.
Qed.

(* TODO: check me, this thing is fully AI-gen'd right now. *)
Theorem controller_correct
  : correct_component lossy_channel (M := M)
    lossy_contract (store_specs (seq msg)) channel_growth.
Proof.
move=> q_abstract q_concrete growth X [psucc m] caller; split.
- apply: th_pre_bindA; first by exact: to_hoare_distinguished_trigger_preI.
  move=> [] q_flip /to_hoare_distinguished_trigger_postE ->;
    last by exact: to_hoare_ret_preI.
  apply: th_pre_bindA=> [| current q_get _].
  + by rewrite to_hoare_ptrigger_preE.
  + apply: th_pre_bindA=> [| [] q_put _].
    * by rewrite to_hoare_ptrigger_preE.
    * exact: to_hoare_ret_preI.
- move=> result q_concrete'.
  rewrite th_post_bindA=> -[success [q_flip [ ]]].
  move/to_hoare_distinguished_trigger_postE=> ->.
  case: success=> /=.
  + rewrite th_post_bindA=> -[current [q_get [+ +]]].
    rewrite to_hoare_ptrigger_postE /= => -[-> <-].
    rewrite th_post_bindA=> -[u [q_put [+ +]]].
    rewrite to_hoare_ptrigger_postE=> -[-> _] /to_hoare_ret_postE=> -[<- <-].
    split; first by left.
    rewrite /channel_growth !size_rcons.
    exact: growth.
  + by move/to_hoare_ret_postE=> [<- <-]; split=> //; right.
Qed.

End lossy_channel.
