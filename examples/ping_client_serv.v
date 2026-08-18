From monae Require Import preamble hierarchy.
From mathcomp Require Import all_boot.
From FreerDPS Require Import all_freerdps ping_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope contract_scope.
Close Scope nat_scope.

(** * Specifying the Ping-Pong Protocol *)

Module Export PingPongM.
(** ** Messages *)
(** ** Client *)

Inductive client_api : effect :=
| SEND : msg -> client_api unit
| WAIT : client_api (option msg).

Section client_program.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Definition send : M unit := ptrigger $ SEND Ping.
Definition wait : M (option msg) := ptrigger WAIT.
Definition C : M (option msg) :=
  send >>= fun=> wait.
End client_program.

(** ** Server *)

Inductive server_api : effect :=
| RPLY : msg -> server_api unit
| RECV : server_api (option msg).

Section server_program.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Definition reply : M unit := ptrigger $ RPLY Pong.
Definition recv : M (option msg) := ptrigger RECV.
Definition S_p : M unit :=
  recv >>= fun inc=> if inc is Some Ping then reply else skip.
Fixpoint loop {X : Type} (fuel : nat) (program : M X) : M unit :=
  match fuel with
  | 0%nat => program >> skip
  | S remaining => program >> loop remaining program
  end.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.
End server_program.
End PingPongM.

Module NetworkChannelMod.

Definition packets := seq msg.

Record N := mk_chan {
  serverQ : packets;
  clientQ : packets;
}.

Definition enqueue (message : msg) (queue : packets) :=
  rcons queue message.

Definition send_to_server (message : msg) (network : N) :=
  {| serverQ := enqueue message (serverQ network);
     clientQ := clientQ network |}.

Definition send_to_client (message : msg) (network : N) :=
  {| serverQ := serverQ network;
     clientQ := enqueue message (clientQ network) |}.

Definition receive_from_server (network : N) :=
  match clientQ network with
  | [::] => network
  | _ :: remaining =>
      {| serverQ := serverQ network;
         clientQ := remaining |}
  end.

Definition receive_from_client (network : N) :=
  match serverQ network with
  | [::] => network
  | _ :: remaining =>
      {| serverQ := remaining;
         clientQ := clientQ network |}
  end.

Lemma server_does_not_consume_its_send network :
  serverQ (receive_from_server network) = serverQ network.
Proof. by rewrite /receive_from_server; case: (clientQ network). Qed.

Lemma client_does_not_consume_its_send network :
  clientQ (receive_from_client network) = clientQ network.
Proof. by rewrite /receive_from_client; case: (serverQ network). Qed.

End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

(** ** Client Specification *)

Module ccm.

Definition c_step (network : N) :
    forall X, client_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | SEND message => send_to_server message network
    | WAIT => receive_from_server network
    end.

Definition c_o_caller (network : N) : forall X, client_api X -> Prop :=
  fun X op =>
    match op with
    | SEND _ => True
    | WAIT => exists remaining, clientQ network = Pong :: remaining
    end.

Definition c_o_callee (network : N) :
    forall X, client_api X -> X -> Prop :=
  fun X op =>
    match op in client_api X return X -> Prop with
    | SEND _ => fun _ => True
    | WAIT => fun result =>
        exists remaining,
          clientQ network = Pong :: remaining /\
          (result = Some Pong \/ result = None)
    end.

Definition c_contract : contract client_api N :=
  make_contract c_step c_o_caller c_o_callee.


Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma c_respect
    (network : N) (remaining : packets)
    (Pong_available : clientQ network = Pong :: remaining) :
  pre (c_contract ||> C) network.
Proof.
apply: th_pre_bindA=>[|? ω'];
  rewrite to_hoare_ptrigger_preE ?to_hoare_ptrigger_postE.
- by [].
by move=>[-> _]; exists remaining.
Qed.

Lemma c_run
    (initial_network final_network : N) (message : option msg)
    (run : post (c_contract ||> C)
      initial_network message final_network) :
  message = Some Pong \/ message = None.
Proof.
move: run; rewrite th_post_bindA=> -[[] [network []]].
rewrite to_hoare_ptrigger_postE /= => -[-> _].
rewrite to_hoare_ptrigger_postE /= => -[_].
by move=> [? [_ result]].
Qed.

End client_respectful_and_run_lemmas.

End ccm.

(** ** Server Specification *)

Module scm.

Definition s_step (network : N) :
    forall X, server_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | RPLY message => send_to_client message network
    | RECV => receive_from_client network
    end.

Definition s_o_caller (network : N) : forall X, server_api X -> Prop :=
  fun X op => True.

Definition s_o_callee (network : N) :
    forall X, server_api X -> X -> Prop :=
  fun X op =>
    match op in server_api X return X -> Prop with
    | RECV => fun result => result = Some Ping \/ result = None
    | RPLY _ => fun _ => True
    end.

Definition s_contract : contract server_api N :=
  make_contract s_step s_o_caller s_o_callee.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma s_p_respect (network : N) :
  pre (s_contract ||> S_p) network.
Proof.
by apply: th_pre_bindA=>[| [[]|]*];
  rewrite ?to_hoare_ptrigger_preE //;
  exact: to_hoare_ret_preI.
Qed.

Lemma s_respect (network : N) fuel :
  pre (s_contract ||> S_ fuel) network.
Proof.
move: fuel network;
  elim=> [|n ih] ?;
    (apply: th_pre_bindA=>*; [exact: s_p_respect| ]).
- exact: to_hoare_ret_preI.
- exact: ih.
Qed.

Lemma s_p_run_grows
  (initial_network final_network : N) (result : unit)
  (run : post (s_contract ||> S_p)
    initial_network result final_network) :
clientQ final_network = clientQ initial_network
  \/ clientQ final_network = rcons (clientQ initial_network) Pong.
Proof.
move: run; rewrite th_post_bindA.
by move=> [incoming [network []]];
  rewrite to_hoare_ptrigger_postE=> -[-> []] ->;
  rewrite ?to_hoare_ptrigger_postE ?to_hoare_ret_postE;
    [ move=>[-> _] /=; right | move=>[_ <-]; left ];
  rewrite client_does_not_consume_its_send.
Qed.

Lemma s_p_run_growth
    (initial_network final_network : N) (result : unit)
    (run : post (s_contract ||> S_p)
      initial_network result final_network) :
  exists delivered,
    delivered <= 1 /\
    size (clientQ final_network) =
      size (clientQ initial_network) + delivered.
Proof.
have [-> | ->] := s_p_run_grows run.
- by exists 0%nat; split=>//; rewrite addn0.
- by exists 1%nat; split=>//; rewrite size_rcons addn1.
Qed.

Lemma s_run
    (initial_network final_network : N) (result : unit) fuel
    (run : post (s_contract ||> S_ fuel)
      initial_network result final_network) :
  size (clientQ final_network) <= size (clientQ initial_network) + (fuel.+1).
  (* size (clientQ final_network) <=
     size (clientQ initial_network ++ nseq (fuel.+1) Pong). *)
Proof.
move: fuel initial_network final_network run;
  elim=> [|n ih] initial_network ?;
  rewrite th_post_bindA=> -[ [] [net [Ha ]] ];
  have [x [Hx Hg]] := s_p_run_growth Ha.
(* - by rewrite to_hoare_ret_postE cats1 /==> -[? <-]; rewrite Hy size_rcons. *)
- by rewrite to_hoare_ret_postE=> -[? <-]; rewrite Hg leq_add.
by move=> H_loop; have ih' := (ih _ _ H_loop); apply: (leq_trans ih');
  rewrite Hg !addnS addnAC -addn2 ltn_add2l; exact: Hx.
Qed.

End server_respectful_and_run_lemmas.
End scm.

Import ccm scm.


(** * Protocol Description :
       +---+  == send Ping ==>  +---+  == deliver Ping ==>  +---+
       | C |                    | N |                        | S |
       +---+  <== get Pong ==   +---+  <== reply Pong =====  +---+
*)
Module ProtocolM.
Section proto_s.

Inductive proto_api : effect := one_round : proto_api outcome.

Context {ProtoF : effect} `{StrictProvide2 ProtoF client_api server_api}
(* `{client_api -< ProtoF, server_api -< ProtoF} *)
  {M : freerMonad ProtoF}.
Definition c : contract ProtoF N := c_contract -^- s_contract.

Local Notation "c ||> p" := (to_hoare (M:=M) c p) (at level 90).

(* Definition proto {outputF : effect} : component outputF ProtoF. *)

Definition protocol : component (M:=M) proto_api ProtoF :=
  fun _ op =>
    match op with
    | one_round =>
        send >> recv  >>= fun incoming =>
          match incoming with
          | Some Ping =>  reply >> wait >>= fun incoming =>
            match incoming with
            | Some Pong => Ret GotPong
            | _ => Ret LostPong
            end
          | _ => Ret LostPing
          end
    end.

Definition protocol_inv (net : N) := serverQ net = [::] /\ clientQ net = [::].

Lemma protocol_respect (net : N) :
  protocol_inv net -> pre (c ||> protocol one_round) net.
Proof.
move=>[s_empty c_empty].
rewrite /protocol !bindA.
apply/th_pre_bindA=>[|??];
  first by apply/to_hoare_shared_contract_left_trigger_preI.

move/to_hoare_shared_contract_left_trigger_postE=>[-> _].
apply/th_pre_bindA=>[|r?];
  first by apply/to_hoare_shared_contract_right_trigger_preI.

move/to_hoare_shared_contract_right_trigger_postE=>[-> _].
case : r => [[]|]; try exact: to_hoare_ret_preI.

apply/th_pre_bindA=>[|??];
  first by apply/to_hoare_shared_contract_right_trigger_preI.
move/to_hoare_shared_contract_right_trigger_postE=>[-> _].

apply/th_pre_bindA=>[|r?].
apply/to_hoare_shared_contract_left_trigger_preI; exists [::].
- by rewrite /= client_does_not_consume_its_send c_empty.
- by move/to_hoare_shared_contract_left_trigger_postE=>[-> _];
      case : r => [[]|]; exact: to_hoare_ret_preI.
Qed.

Lemma protocol_run_inv (n n' : N) (result : outcome) :
  protocol_inv n -> post (c |> protocol one_round) n result n' ->
   protocol_inv n'.
Proof.
move=> [server_empty client_empty].
rewrite /protocol !bindA th_post_bindA=> -[[] [? []]].
rewrite to_hoare_shared_contract_left_trigger_postE=> -[-> _].
move/th_post_bindA=>[incoming [? []]].
rewrite to_hoare_shared_contract_right_trigger_postE=> -[-> incoming_ok].
case: incoming_ok=> -> //=.
move/th_post_bindA=>[[] [? []]] /=;
rewrite to_hoare_shared_contract_right_trigger_postE=> -[-> _];
move/th_post_bindA=>[wait_result [? []]];
rewrite to_hoare_shared_contract_left_trigger_postE=> -[-> [? [_ incoming_ok]]] /=;
case: incoming_ok=> ->.
all: by rewrite to_hoare_ret_postE=> -[_ <-] /=;
  rewrite /send_to_server client_empty server_empty
    ?client_does_not_consume_its_send.
Qed.

Lemma proto_correct :
  correct_component protocol (no_contract proto_api) c
    (fun=> protocol_inv).
Proof.
move=>[] n inv ? [] []; split=>[|m n' Hpost] /=.
  exact: protocol_respect.
by split=>//; move: (protocol_run_inv inv Hpost).
Qed.

End proto_s.
End ProtocolM.

(** * Probability of Success *)

(******************************************************************************)
(* TODO: Rewrite the above using FlipEff instead of `proto_api`, normally the *)
(*       proofs should be quite straightforward (reusing ping_freer_prob.v at *)
(*      most points).                                                         *)
(******************************************************************************)

(**
A network transmission succeeds with probability [1 - p]. Packet losses are
independent. For one round trip:

<<
P(Pong received) = P(Ping delivered) * P(Pong delivered)
                 = (1 - p) * (1 - p)
                 = (1 - p)^2.
>>

For at most [n] attempts, with [q = (1 - p)^2]:

<<
P(n) = 1 - (1 - q)^n.
>>
*)
