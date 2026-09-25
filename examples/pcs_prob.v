From mathcomp Require Import boot order algebra interval_inference.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import all_freerdps ping_common ping_client_serv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
(*   |   two components together.                                             *)
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

Definition flip_step (server_bound : bool) (network : net_state) :
    forall X, @FlipEff R X -> X -> net_state :=
  fun X op =>
    match op in FlipEff X return X -> net_state with
    | flipe _ => fun keep =>
        drop_new_packet network keep server_bound
    end.

Definition selected_queue (server_bound : bool) (network : net_state) :
    packets :=
  if server_bound then serverQ network else clientQ network.

Definition flip_o_caller (server_bound : bool) (network : net_state) :
    forall X, @FlipEff R X -> Prop :=
  fun _ _ =>
    exists remaining packet,
      selected_queue server_bound network =
        rcons remaining packet /\
      can_still_be_dropped packet = true.

Definition flip_transition
    (server_bound : bool) (network : net_state) (keep : bool) : Prop :=
  exists remaining packet,
    selected_queue server_bound network = rcons remaining packet /\
    selected_queue server_bound
      (drop_new_packet network keep server_bound) =
      if keep then rcons remaining (deliver packet) else remaining.

Definition flip_o_callee (server_bound : bool) (network : net_state) :
    forall X, @FlipEff R X -> X -> Prop :=
  fun X op =>
    match op in FlipEff X return X -> Prop with
    | flipe _ => flip_transition server_bound network
    end.

Definition flip_contract (server_bound : bool) :
    contract (@FlipEff R) net_state :=
  make_contract (flip_step server_bound)
    (flip_o_caller server_bound) (flip_o_callee server_bound).

End flip_contract.
Section syntax.
Context {R: realType} {Fx : effect} `{@FlipEff R -< Fx}.
Context {M : freerMonad Fx}.

Lemma syn_flip (p : {prob R}) : providesOnlyF (F:=@FlipEff R) (M := M) (flip p).
Proof. by exists (frTrigger (inj (flipe p))). Qed.

End syntax.

#[export] Hint Extern 0 (providesOnlyF (F:=FlipEff) (flip _)) =>
  solve [exact: syn_flip] : core.

(** * Probabilistic Ping-Pong Programs *)

Module Export ProbPingPongM.

(** ** Client *)

Section client_program.
Context {R : realType} {Fx : effect}.
Context `{@FlipEff R ;; client_api -<< Fx} {M : freerMonad Fx}.

Definition transmit (psucc : {prob R}) (program : M unit) : M unit :=
  program >> (flip psucc >> Ret tt).

Variable (psucc : {prob R}).

Definition lossy_send : M unit := transmit psucc send.
Definition C : M (option msg) := lossy_send >>= fun=> wait.
End client_program.

(** ** Server *)

Section server_program.
Context {R : realType} {Fx : effect}.
Context `{@FlipEff R ;; server_api -<< Fx} {M : freerMonad Fx}.

Variable (psucc : {prob R}).

Definition lossy_reply : M bool := reply >> flip psucc.
Definition S_p : M (option msg) :=
  recv >>= fun inc=>
    if inc is Some Ping then lossy_reply >> Ret inc else Ret inc.
Abbreviation loop := PingPongM.loop.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.
Arguments S_p : simpl never.
End server_program.
End ProbPingPongM.

Import ccm scm.

(** ** Packet Delivery Specification *)

Section flip_respectful_and_run_lemmas.
Context {R : realType} {Fx : effect} `{@FlipEff R -< Fx}.
Context {M : freerMonad Fx}.
Implicit Types (psucc : {prob R}).

Fact flip_respect server_bound psucc (net : net_state) remaining packet
    (queued : selected_queue server_bound net = rcons remaining packet)
    (droppable : can_still_be_dropped packet = true) :
  pre (@flip_contract R server_bound |> (flip psucc : M _)) net.
Proof.
rewrite to_hoare_triggerE /= provided_callerP /=.
by exists remaining, packet.
Qed.

Fact flip_run server_bound psucc (ins fns : net_state) keep
    (run : post (@flip_contract R server_bound |> (flip psucc : M _))
      ins keep fns) :
  fns = drop_new_packet ins keep server_bound.
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP=> -[].
Qed.
End flip_respectful_and_run_lemmas.

(** ** Client Specification *)

Module pccm.
Section client_respectful_and_run_lemmas.
Context {R : realType} {Fx ClientF: effect}.
Context `{@FlipEff R ;; client_api -<< Fx} `{ClientF -< Fx} {M : freerMonad Fx}.

Implicit Types (psucc : {prob R}).


Fact lossy_send_respect psucc (net : net_state) :
  pre (@flip_contract R true -^- client_c |> (lossy_send psucc : M _)) net.
Proof.
rewrite !freer_to_hoare_bindE freer_contract_right //.
split; first exact: send_respect.
move=> [] [sQ cQ] /send_run /= [-> ->].
rewrite freer_contract_left //.
split.
- exact: flip_respect.
- by move=> *; rewrite pre_ret.
Qed.

Fact lossy_send_run psucc (ins fns : net_state) (u : unit)
    (run : post (@flip_contract R true -^- client_c |> (lossy_send psucc : M _)) ins u fns) :
  fns.(clientQ) = ins.(clientQ) /\
  (fns.(serverQ) = rcons ins.(serverQ) !-Ping \/
   fns.(serverQ) = ins.(serverQ)).
Proof.
move: run.
rewrite !freer_to_hoare_bindE freer_contract_right //.
case=> [[]] [[sQ cQ]] [] /send_run /= [-> ->].
rewrite freer_contract_left //.
case=> [keep] [net] [] /flip_run ->.
rewrite post_ret=> -[_ <-] /=.
by rewrite drop_last_rcons; case: keep; split=> //; [left | right].
Qed.

Lemma c_respect psucc (net : net_state) (remaining : packets)
    (coh : clientQ net = !-Pong :: remaining \/ clientQ net = [::]) :
  pre (@flip_contract R true -^- client_c |> (C psucc : M _)) net.
Proof.
rewrite /C freer_to_hoare_bindE; split.
  exact: lossy_send_respect.
move=> [] [sQ cQ] /lossy_send_run /= [-> _].
rewrite freer_contract_right //.
exact/wait_respect/coh.
Qed.

Lemma c_run psucc (ins fns : net_state) (result : option msg)
    (run : post (@flip_contract R true -^- client_c |> (C psucc : M _)) ins result fns) :
  fns.(clientQ) = behead ins.(clientQ) /\
  (fns.(serverQ) = rcons ins.(serverQ) !-Ping \/
   fns.(serverQ) = ins.(serverQ)).
Proof.
move: run; rewrite freer_to_hoare_bindE.
case=> [[]] [[sQ cQ]] [] /lossy_send_run /= [-> sent].
rewrite freer_contract_right //.
by move/wait_run=> /= [-> ->].
Qed.
End client_respectful_and_run_lemmas.
End pccm.

(** ** Server Specification *)

Module pscm.
Section server_respectful_and_run_lemmas.
Context {R : realType} {Fx : effect}.
Context `{@FlipEff R ;; server_api -<< Fx} {M : freerMonad Fx}.

Implicit Types (psucc : {prob R}).

Fact lossy_reply_respect psucc (net : net_state) :
  pre ( @flip_contract R false -^- server_c |> (lossy_reply psucc : M _)) net.
Proof.
rewrite freer_to_hoare_bindE freer_contract_right //.
split; first exact: reply_respect.
move=> [] [sQ cQ] /reply_run /= [-> ->].
rewrite freer_contract_left //.
exact: flip_respect.
Qed.

Fact lossy_reply_run psucc (ins fns : net_state) keep
    (run : post ( @flip_contract R false -^- server_c |> (lossy_reply psucc : M _)) ins keep fns) :
  fns.(clientQ) =
    (if keep then rcons ins.(clientQ) !-Pong else ins.(clientQ)) /\
  fns.(serverQ) = ins.(serverQ).
Proof.
move: run; rewrite freer_to_hoare_bindE freer_contract_right //.
case=> [[]] [[sQ cQ]] [] /reply_run /= [-> ->].
rewrite freer_contract_left //.
by move/flip_run=> -> /=; rewrite drop_last_rcons.
Qed.

Lemma s_p_respect psucc (net : net_state) (remaining : packets)
    (coh : serverQ net = !-Ping :: remaining \/ serverQ net = [::]) :
  pre ( @flip_contract R false -^- server_c |> (S_p psucc : M _)) net.
Proof.
rewrite freer_to_hoare_bindE freer_contract_right //.
split; first exact/recv_respect/coh.
move=> [[]|] [sQ cQ] /recv_run /= [-> ->].
- rewrite freer_to_hoare_bindE; split.
  + exact: lossy_reply_respect.
  + move=> *.
all: by rewrite pre_ret.
Qed.

Lemma s_p_run psucc (ins fns : net_state) (result : option msg)
    (run : post ( @flip_contract R false -^- server_c |> (S_p psucc : M _)) ins result fns) :
  (match result with
   | Some Ping => fns.(clientQ) = ins.(clientQ) \/
                  fns.(clientQ) = rcons ins.(clientQ) !-Pong
   | _ => fns.(clientQ) = ins.(clientQ)
   end) /\ fns.(serverQ) = behead ins.(serverQ).
Proof.
move: run; rewrite freer_to_hoare_bindE.
rewrite freer_contract_right //.
case=> [[[]|]] [[sQ cQ]] [] /recv_run /= [-> ->].
- rewrite freer_to_hoare_bindE.
  case=> [keep] [[sQ' cQ']] [] /lossy_reply_run /= [-> ->].
  rewrite post_ret=> -[<- <-] /=.
  by case: keep; split=> //; [right | left].
all: by rewrite post_ret=> -[<- <-].
Qed.

Lemma s_p_run_growth psucc (ins fns : net_state) (result : option msg)
    (run : post ( @flip_contract R false -^- server_c |> (S_p psucc : M _)) ins result fns) :
  exists delivered : nat,
    delivered <= 1 /\
    size (clientQ fns) = size (clientQ ins) + delivered.
Proof.
have [replied _] := s_p_run run.
clear run.
case: result replied=> [[|]|] /=.
- case=> ->.
    by exists 0; split=> //; rewrite addn0.
  by exists 1; split=> //; rewrite size_rcons addn1.
all: by move=> ->; exists 0; split=> //; rewrite addn0.
Qed.

(** Every queued request is ready to be received. *)
Definition server_ready (net : net_state) : bool :=
  all (fun packet=>
    if packet is mk_p Ping false then true else false) (serverQ net).

Lemma s_respect psucc fuel (net : net_state) :
  server_ready net -> pre ( @flip_contract R false -^- server_c |> (S_ psucc fuel : M _)) net.
Proof.
have step_respect ns :
    server_ready ns -> pre ( @flip_contract R false -^- server_c |> (S_p psucc : M _)) ns.
  move=> ready; apply: (@s_p_respect psucc ns (behead (serverQ ns))).
  move: ready; rewrite /server_ready.
  case: (serverQ ns)=> [|[[] []] remaining] //=.
    by move=> _; right.
  by move=> _; left.
move: fuel net; elim=> [|fuel IHfuel] net ready.
- rewrite /S_ /= freer_to_hoare_bindE; split.
    exact: step_respect ready.
  by move=> *; rewrite pre_skip.
rewrite /S_ /= freer_to_hoare_bindE; split.
  exact: step_respect ready.
move=> result net' /s_p_run [_ queues].
apply: IHfuel.
move: ready; rewrite /server_ready queues.
by case: (serverQ net)=> //= packet remaining /andP [].
Qed.

Lemma s_run psucc fuel (ins fns : net_state) (result : unit)
    (run : post ( @flip_contract R false -^- server_c |> (S_ psucc fuel : M _)) ins result fns) :
  size (clientQ fns) <= size (clientQ ins) + fuel.+1.
Proof.
move: fuel ins fns run; elim=> [|fuel IHfuel] ins fns.
- rewrite freer_to_hoare_bindE.
  case=> [r] [net] [step_run].
  have [delivered [delivered_le1 growth]] := s_p_run_growth step_run.
  by rewrite post_skip=> <-; rewrite growth leq_add.
rewrite freer_to_hoare_bindE.
case=> [r] [net] [step_run loop_run].
have [delivered [delivered_le1 growth]] := s_p_run_growth step_run.
apply: leq_trans (IHfuel _ _ loop_run) _.
by rewrite growth !addnS addnAC -addn2 ltn_add2l.
Qed.
End server_respectful_and_run_lemmas.
End pscm.

Import pccm pscm.

Section protocol_contract.
Context {R : realType} {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF}.

Definition sharedP : contract ProtoF net_state :=
  (@flip_contract R true -^- client_c) -^-
  ( @flip_contract R false -^- server_c).
End protocol_contract.

Module Import ProbProtocolSyntax.
Section syntax.
Context {R : realType} {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF} {M : freerMonad ProtoF}.

Lemma syn_lossy_send (psucc : {prob R}) :
  providesOnlyF (F:=ClientF) (M := M) (lossy_send psucc).
Proof.
by exists (frBind (frTrigger (inj (SEND Ping)))
  (fun=> frBind (frTrigger (inj (flipe psucc))) (fun=> frRet tt))).
Qed.

Lemma syn_s_p (psucc : {prob R}) :
  providesOnlyF (F:= ServerF) (M := M) (S_p psucc).
Proof.
exists (frBind (frTrigger (inj RECV)) (fun inc=>
  if inc is Some Ping then
    frBind (frBind (frTrigger (inj (RPLY Pong)))
      (fun=> frTrigger (inj (flipe psucc)))) (fun=> frRet inc)
  else frRet inc)).
rewrite /= /S_p /lossy_reply.
congr (recv >>= _).
by apply: boolp.funext=> -[[]|].
Qed.

End syntax.

#[export] Hint Extern 0 (providesOnlyF (lossy_send _)) =>
  solve [exact: syn_lossy_send] : core.
#[export] Hint Extern 0 (providesOnlyF (S_p _)) =>
  solve [exact: syn_s_p] : core.
End ProbProtocolSyntax.

(** * Protocol Description *)

Module ProbProtocolM.
Section protocol.
Context {R : realType} {ClientF ServerF ProtoF : effect}.
Context `{@FlipEff R ;; client_api -<< ClientF}.
Context `{@FlipEff R ;; server_api -<< ServerF}.
Context `{ClientF ;; ServerF -<< ProtoF} {M : freerMonad ProtoF}.

Variable (psucc : {prob R}).

Inductive proto_api : effect := one_round : proto_api outcome.

Definition protocol : component (M := M) proto_api ProtoF :=
  fun _ cmd=>
    match cmd with
    | one_round =>
        lossy_send psucc >> (S_p psucc >>= fun inc=>
          match inc with
          | Some Ping => wait >>= fun inc=>
              match inc with
              | Some Pong => Ret GotPong
              | _ => Ret LostPong
              end
          | _ => Ret LostPing
          end)
    end.

Definition protocol_contract : contract ProtoF net_state :=
  sharedP (R := R) (ClientF := ClientF) (ServerF := ServerF).

Definition protocol_inv (net : net_state) : Prop :=
  serverQ net = [::] /\ clientQ net = [::].

(** The component lemmas above use a contract on the ambient effect.
    Reusing them here requires lifting through ClientF and ServerF into
    ProtoF, which freer_contract_left/right do not currently support. *)
Lemma protocol_respect (net : net_state) :
  protocol_inv net ->
  pre (protocol_contract |> protocol one_round) net.
Proof.
move=> [s0 c0].
rewrite freer_to_hoare_bindE freer_contract_left // freer_contract_prodT.
split; first by exact: lossy_send_respect.
move=> [] [s1 c1] /lossy_send_run [].
rewrite s0 c0=> /= -> Hs1.
rewrite freer_to_hoare_bindE freer_contract_right // freer_contract_prodT.
split; first by exact/s_p_respect/Hs1.
move=> opm [s2 c2] /s_p_run /=.
case: opm=> [[]|] [] Hc2 -> /=.
rewrite freer_to_hoare_bindE freer_contract_left //.
rewrite freer_contract_prodT freer_contract_right //.
split; first by apply/wait_respect; rewrite /= or_comm; exact: Hc2.
move=> opm [s3 c3] /wait_run /= [-> ->].
case: opm=> [[]|] /=.
all: by rewrite pre_ret.
Qed.

Lemma protocol_run_inv (ins fns : net_state) (result : outcome) :
  protocol_inv ins ->
  post (protocol_contract |> protocol one_round) ins result fns ->
  protocol_inv fns.
Proof.
move=> [s0 c0].
rewrite freer_to_hoare_bindE freer_contract_left // freer_contract_prodT.
case=> [[]] [[s1 c1]] [] /lossy_send_run [].
rewrite s0 c0=> /= -> Hs1.
have Hbs1 : behead s1 = [::] by case: Hs1=> ->.
rewrite freer_to_hoare_bindE freer_contract_right // freer_contract_prodT.
case=> [opm] [[s2 c2]] [] /s_p_run /=.
case: opm=> [[]|] [] Hc2 -> /=.
have Hbc2 : behead c2 = [::] by case: Hc2=> ->.
rewrite freer_to_hoare_bindE freer_contract_left //.
rewrite freer_contract_prodT freer_contract_right //.
case=>[opm] [[s3 c3]] [] /wait_run /= [-> ->].
case: opm=> [[]|] /=.
all: rewrite post_ret=> -[_ <-]; split=> //.
Qed.

Lemma proto_correct :
  correct_component protocol (no_contract proto_api) protocol_contract
    (fun=> protocol_inv).
Proof.
move=> [] net inv ? [] []; split=> [|result net' run] /=.
  exact: protocol_respect.
by split=> //; exact: protocol_run_inv inv run.
Qed.
End protocol.
End ProbProtocolM.
