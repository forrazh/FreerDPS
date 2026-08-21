From mathcomp Require Import all_boot all_order all_algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope contract_scope.

Local Open Scope nat_scope.

(******************************************************************************)
(*                                                                            *)
(* Ok, in this file, what I am trying is to provide the probability as a part *)
(* of the client / server contract and to refine transmit over those effects. *)
(*                                                                            *)
(* To make it a bit more understandable, we currently have 2 working freer    *)
(* implementations :                                                          *)
(* - A freer model using probabilities                      (1) ;             *)
(* - A model using FreeSpec like interfaces/hoare reasoning (2).              *)
(*                                                                            *)
(* The goal here would be to use both at once, thus be able to model and make *)
(* the proofs of (1) using the implem / model of (2), which would further     *)
(* strengthen the confidence we have in our model.                            *)
(*                                                                            *)
(* Current experiment :                                                       *)
(* > Make a new provided effect based on client/serv + FlipEff and write      *)
(*   transmit from this effect. If this work correctly, we should be able to  *)
(*   reuse the ping_common.v file without any issue and this should be a good *)
(*   direction to write new systems with a probabilistic direction.           *)
(*                                                                            *)
(* The last experiments that were done :                                      *)
(* - Linking the probability to the channel directly                          *)
(*   +-> This makes sense because the client should not know when sending or  *)
(*   |   receiving that the message has been dropped. The actual mechanism    *)
(*   |   should be built through another mechansim *)
(*   +-> This works on a component and we currently have no way of linking    *)
(*   |   two components together.                    .                         *)
(*   +-> This could be an interesting research track though.                  *)
(*                                                                            *)
(* *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ** *)
(*                                                                            *)
(* Inner feeling :                                                            *)
(* - I think that their are two things (or maybe more) to take in account for *)
(*   probabilities :                                                          *)
(*   + the client should not make the prob choice of sending the message      *)
(*     unless it comes from a client's failure or malfunction or anything;    *)
(*   + the network should handle the packet drops, but here that's probably   *)
(*     not a freer monad as the network we use is a state... or maybe we can  *)
(*     find a way to cheat our way out ? <== I think that's what happened...  *)
(*   + Probabilities modeled by byzantine adversaries might fall in a 3rd     *)
(*     category... Or a mix of multiple...                                    *)
(*                                                                            *)
(******************************************************************************)

Import NetworkChannelMod.

Section flip_contract.
Context {R : realType}.

Definition flip_step (server_bound : bool) (network : N) :
    forall X, @FlipEff R X -> X -> N :=
  fun X op =>
    match op in FlipEff X return X -> N with
    | flipe _ => fun keep =>
        drop_new_packet network keep server_bound
    end.

Definition selected_queue (server_bound : bool) (network : N) : packets :=
  if server_bound then serverQ network else clientQ network.

Definition flip_o_caller (server_bound : bool) (network : N) :
    forall X, @FlipEff R X -> Prop :=
  fun _ _ =>
    exists remaining packet,
      selected_queue server_bound network =
        rcons remaining packet /\
      can_still_be_dropped packet = true.

Definition flip_transition
    (server_bound : bool) (network : N) (keep : bool) : Prop :=
  exists remaining packet,
    selected_queue server_bound network = rcons remaining packet /\
    selected_queue server_bound
      (drop_new_packet network keep server_bound) =
      if keep then rcons remaining (deliver packet) else remaining.

Definition flip_o_callee (server_bound : bool) (network : N) :
    forall X, @FlipEff R X -> X -> Prop :=
  fun X op =>
    match op in FlipEff X return X -> Prop with
    | flipe _ => flip_transition server_bound network
    end.

Definition flip_contract (server_bound : bool) :
    contract (@FlipEff R) N :=
  make_contract (flip_step server_bound)
    (flip_o_caller server_bound) (flip_o_callee server_bound).

End flip_contract.


Import ccm.

Section client_prob_s.
Context {R : realType} {Fx : effect}
(* `{@FlipEff R -< Fx, client_api -< Fx} *)
`{StrictProvide2 Fx (@FlipEff R) client_api}
 {M : freerMonad Fx}.

Definition transmit (p: {prob R}) (ef : Fx msg) : M (option msg) :=
trigger msg ef >>= fun m => Ret (Some m) <|| p ||> Ret None.
Implicit Types (m : msg).
Variable (psucc : {prob R}).

Definition send : M unit := ptrigger $ SEND Ping.
Definition lossy_send : M unit := send >> flip psucc >> Ret tt.
Definition wait : M (option msg) := ptrigger WAIT.
Definition C : M (option msg) :=
  lossy_send >>= fun=> wait.
End client_prob_s.

Section tmp.
Context {R : realType} {Fx : effect} `{StrictProvide2 Fx (@FlipEff R) client_api}
 {M : freerMonad Fx}.
Definition sharedC : contract Fx N :=
  (@flip_contract R true) -^- c_contract.

Implicit Types (m : msg) (psucc : {prob R}).

Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).
Lemma c_respect psucc
    (network : N) (remaining : packets)
    (Pong_available : clientQ network = ?-Pong :: remaining) :
  pre (sharedC ||> C psucc) network.
Proof.
apply: th_pre_bindA=>[|? ω'].
- apply: th_pre_bindA=>[|? ω'].
  + apply: th_pre_bindA=>[|? ω'];
      first by apply/to_hoare_shared_contract_right_trigger_preI.
    rewrite /=.
    move/to_hoare_shared_contract_right_trigger_postE=> /= [-> _].
    apply/to_hoare_shared_contract_left_trigger_preI.

    rewrite /= /send_to_server /flip_o_caller /selected_queue /enqueue /=.
    by exists (serverQ network), (?- Ping).
  + move=>?; exact: to_hoare_ret_preI.
- rewrite th_post_bindA=>-[?[? []]]; rewrite th_post_bindA=>-[? [? []]].
  move/to_hoare_shared_contract_right_trigger_postE=> /= [-> _];
    move/to_hoare_shared_contract_left_trigger_postE=> /= [-> _];
    move/to_hoare_ret_postE=>/=[_ <-].
  rewrite Pong_available; apply/to_hoare_shared_contract_right_trigger_preI=>/=.
  by exists remaining.
Qed.

Lemma c_run psucc
    (initial_network final_network : N) (p : option msg)
    (run : post (sharedC ||> C psucc)
      initial_network p final_network) :
  p = Some Pong \/ p = None.
Proof.
by move: run;
  rewrite th_post_bindA=> -[[] [n []]];
  rewrite th_post_bindA=> -[[] [n' []]];
  rewrite th_post_bindA=> -[[] [n'' []]];
  move/to_hoare_shared_contract_right_trigger_postE=> /= [-> ?];
  move/to_hoare_shared_contract_left_trigger_postE=> /= [-> /= ?];
  move/to_hoare_ret_postE=>/=[_ <-];
  rewrite to_hoare_shared_contract_right_trigger_postE=>/= -[+ [rmn []]].
Qed.

End tmp.


Import scm.

Section server_prob_s.
Context {R : realType} {Fx : effect}
  `{StrictProvide2 Fx (@FlipEff R) server_api}
  {M : freerMonad Fx}.

Variable (psucc : {prob R}).

Definition recv : M (option msg) := ptrigger RECV.
Definition reply : M unit := ptrigger $ RPLY Pong.
Definition lossy_reply : M unit :=
  reply >> flip psucc >> Ret tt.
Definition S_p : M unit :=
  recv >>= fun incoming =>
    if incoming is Some Ping then lossy_reply else Ret tt.
Fixpoint loop {X : Type} (fuel : nat) (program : M X) : M unit :=
  match fuel with
  | 0%nat => program >> Ret tt
  | S remaining => program >> loop remaining program
  end.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.

End server_prob_s.

Section server_contract.
Context {R : realType} {Fx : effect}
  `{StrictProvide2 Fx (@FlipEff R) server_api}
  {M : freerMonad Fx}.

Definition sharedS : contract Fx N :=
  (@flip_contract R false) -^- s_contract.

Implicit Types (psucc : {prob R}).

Local Notation "c ||> p" := (to_hoare (M := M) c p)
  (at level 50, no associativity).

Lemma s_p_respect psucc (network : N) :
  pre (sharedS ||> S_p psucc) network.
Proof.
apply: th_pre_bindA=>[|x ?];
      first by apply/to_hoare_shared_contract_right_trigger_preI.
move/to_hoare_shared_contract_right_trigger_postE=> /= [-> _]; case: x=>[[]|];
  try exact/to_hoare_ret_preI.

apply: th_pre_bindA=>[|x ?].
- apply: th_pre_bindA=>[|??];
      first by exact/to_hoare_shared_contract_right_trigger_preI.
  move/to_hoare_shared_contract_right_trigger_postE=> /= [-> _];
    apply/to_hoare_shared_contract_left_trigger_preI=>/=.
  rewrite /send_to_server /flip_o_caller /= client_does_not_consume_its_send.
  by exists (clientQ network), (?- Pong).
- rewrite th_post_bindA=>-[?[? []]];
    move/to_hoare_shared_contract_right_trigger_postE=> /= [-> _];
    move/to_hoare_shared_contract_left_trigger_postE=> /= [-> _].
    exact/to_hoare_ret_preI.
Qed.

Lemma s_respect psucc (network : N) fuel :
  pre (sharedS ||> S_ psucc fuel) network.
Proof.
move: fuel network; elim=>[|? ih]?;
  (apply/th_pre_bindA=>[|*]; [exact: s_p_respect |]).
- exact: to_hoare_ret_preI.
- exact: ih.
Qed.

Lemma s_p_run
    (initial_network final_network : N) (result : unit) psucc
    (run : post (sharedS ||> S_p psucc)
      initial_network result final_network) :
  clientQ final_network = clientQ initial_network \/
  clientQ final_network = rcons (clientQ initial_network) !-Pong.
Proof.
move: run.
rewrite th_post_bindA=> -[may_msg [? []]].
move/to_hoare_shared_contract_right_trigger_postE=> /= [-> [->|->]];
  last by move/to_hoare_ret_postE=>/=[_ <-] //=;
    rewrite client_does_not_consume_its_send; left.
by rewrite th_post_bindA=> -[[] [? []]];
  rewrite th_post_bindA=> -[[] [? []]];
  move/to_hoare_shared_contract_right_trigger_postE=> [-> ?];
  move/to_hoare_shared_contract_left_trigger_postE=> [-> ?];
  move/to_hoare_ret_postE=>/= [_ <-];
  rewrite client_does_not_consume_its_send drop_last_rcons; [right|left].
Qed.

Lemma s_p_run_growth
    (initial_network final_network : N) (result : unit) psucc
    (run : post (sharedS ||> S_p psucc)
      initial_network result final_network) :
  exists (delivered: nat),
    delivered <= 1 /\
    size (clientQ final_network) =
      size (clientQ initial_network) + delivered.
Proof.
have [-> | ->] := s_p_run _ _ _ psucc run.
- by exists 0%nat; split=>//; rewrite addn0.
- by exists 1%nat; split=>//; rewrite size_rcons addn1.
Qed.


Lemma s_run
    (initial_network final_network : N) (result : unit) psucc fuel
    (run : post (sharedS ||> S_ psucc fuel)
      initial_network result final_network) :
  (size (clientQ final_network) <=
    size (clientQ initial_network) + fuel.+1)%nat.
Proof.
move: fuel initial_network final_network run;
  elim=> [|n ih] initial_network ?;
  rewrite th_post_bindA=> -[ [] [net [Ha ]] ];
  have [x [Hx Hg]] := s_p_run_growth _ _ _ _ Ha.
(* - by rewrite to_hoare_ret_postE cats1 /==> -[? <-]; rewrite Hy size_rcons. *)
- by rewrite to_hoare_ret_postE=> -[? <-]; rewrite Hg leq_add.
by move=> H_loop; have ih' := (ih _ _ H_loop); apply: (leq_trans ih');
  rewrite Hg !addnS addnAC -addn2 ltn_add2l; exact: Hx.
Qed.

End server_contract.


Section protocol_contract.
Context {R : realType} {ClientF ServerF ProtoF : effect}
  `{StrictProvide2 ClientF (@FlipEff R) client_api}
  `{StrictProvide2 ServerF (@FlipEff R) server_api}
  `{StrictProvide2 ProtoF ClientF ServerF}.

Definition sharedP : contract ProtoF N :=
  (sharedC (R := R) (Fx := ClientF)) -^-
  (sharedS (R := R) (Fx := ServerF)).

End protocol_contract.


Module ProbProtocolM.
Section protocol.
Context {R : realType} {ClientF ServerF ProtoF : effect}
  `{StrictProvide2 ClientF (@FlipEff R) client_api}
  `{StrictProvide2 ServerF (@FlipEff R) server_api}
  `{StrictProvide2 ProtoF ClientF ServerF}
  {M : freerMonad ProtoF}.

Variable (psucc : {prob R}).

Local Notation "c ||> p" := (to_hoare (M := M) c p)
  (at level 50, no associativity).

Inductive proto_api : effect :=
| one_round : proto_api outcome.

Definition trigger_client {X} (op : client_api X) : M X :=
  trigger X (inj (Fx := ProtoF) (inj (Fx := ClientF) op)).

Definition trigger_server {X} (op : server_api X) : M X :=
  trigger X (inj (Fx := ProtoF) (inj (Fx := ServerF) op)).

Definition flip_client : M bool :=
  trigger bool
    (inj (Fx := ProtoF) (inj (Fx := ClientF) (flipe psucc))).

Definition flip_server : M bool :=
  trigger bool
    (inj (Fx := ProtoF) (inj (Fx := ServerF) (flipe psucc))).

Program Definition protocol : component (M := M) proto_api ProtoF :=
  fun _ op => _.
Next Obligation.
case : op.
apply: bind.
apply: lossy_send psucc.

    match op with
    | one_round =>
        lossy_send (M:=M) psucc >> flip_client >>
        trigger_server RECV >>= fun incoming =>
          match incoming with
          | Some Ping =>
              trigger_server (RPLY Pong) >> flip_server >>
              trigger_client WAIT >>= fun incoming =>
                if incoming is Some Pong then
                  Ret GotPong
                else
                  Ret LostPong
          | _ => Ret LostPing
          end
    end.

Definition protocol_contract : contract ProtoF N :=
  sharedP (R := R) (ClientF := ClientF)
    (ServerF := ServerF) (ProtoF := ProtoF).

Definition protocol_component : component (M := M) proto_api ProtoF :=
  protocol.

Definition protocol_inv (network : N) : Prop :=
  serverQ network = [::] /\ clientQ network = [::].

Lemma protocol_respect (network : N) :
  protocol_inv network ->
  pre (protocol_contract ||>
    protocol_component outcome one_round) network.
Admitted.

Lemma protocol_run_inv
    (initial_network final_network : N) (result : outcome) :
  protocol_inv initial_network ->
  post (protocol_contract ||>
    protocol_component outcome one_round)
    initial_network result final_network ->
  protocol_inv final_network.
Admitted.

Lemma proto_correct :
  correct_component protocol_component
    (no_contract proto_api) protocol_contract
    (fun=> protocol_inv).
Admitted.

End protocol.
End ProbProtocolM.
