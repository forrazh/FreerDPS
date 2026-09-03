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
Definition S_p : M (option msg) :=
  recv >>= fun inc=> if inc is Some Ping then reply >> Ret inc else Ret inc.
Fixpoint loop {X : Type} (fuel : nat) (program : M X) : M unit :=
  match fuel with
  | 0%nat => program >> skip
  | S remaining => program >> loop remaining program
  end.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.
End server_program.
End PingPongM.

Module NetworkChannelMod.

Record packet := mk_p {
  m : msg;
  can_still_be_dropped: bool
}.

Implicit Type p : packet.

Definition new_packet_non_drop (m : msg) := mk_p m false.
Notation "!- m" := (new_packet_non_drop m) (at level 1).
Definition new_packet_may_drop (m : msg) := mk_p m true.
Notation "?- m" := (new_packet_may_drop m) (at level 1).

Definition packets := seq packet.

Record N := mk_chan {
  serverQ : packets;
  clientQ : packets;
}.

Definition enqueue p (queue : packets) :=
  rcons queue p.

Definition send_to_server p (network : N) :=
  {| serverQ := enqueue p (serverQ network);
     clientQ := clientQ network |}.

Definition send_to_client p (network : N) :=
  {| serverQ := serverQ network;
     clientQ := enqueue p (clientQ network) |}.

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

Definition deliver p := match p with
| mk_p m _ => !-m
end.
Notation "!!- x" := (deliver x) (at level 1).


Fixpoint drop_last (ps : packets) (keep:bool) := match ps with
| [::] => [::]
| [::x] => if keep then [:: !!-x] else [::]
| [:: h & pps] => [::h & drop_last pps keep]
end.

Lemma drop_last_rcons ps p keep :
  drop_last (rcons ps p) keep =
    if keep then rcons ps (deliver p) else ps.
Proof.
elim: ps keep=> [|first_packet ps ih] keep; first by case: keep.
rewrite rcons_cons.
have rconsE :
    rcons ps p = head p ps :: behead (rcons ps p) :=
  headI ps p.
have drop_last_cons x y tail keep' :
    drop_last (x :: y :: tail) keep' =
      x :: drop_last (y :: tail) keep'.
  by [].
rewrite rconsE drop_last_cons -rconsE ih.
by case: keep.
Qed.

Definition drop_from_serv (n : N)(keep : bool) := match n with
| mk_chan srvQ cliQ => {|serverQ:= drop_last srvQ keep; clientQ:= cliQ|}
end.

Definition drop_from_cli (n : N) (keep : bool) := match n with
| mk_chan srvQ cliQ => {|serverQ:= srvQ; clientQ:= drop_last cliQ keep|}
end.

Definition drop_new_packet (n : N) (keep: bool) (q: bool) :=
if q then drop_from_serv n keep
else drop_from_cli n keep.

End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

(** ** Client Specification *)

Module ccm.

Definition c_step (network : N) :
    forall X, client_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | SEND p => send_to_server ?-p network
    | WAIT => receive_from_server network
    end.

Definition c_o_caller (network : N) : forall X, client_api X -> Prop :=
  fun X op =>
    match op with
    | SEND _ => True
    | WAIT => exists remaining, clientQ network = !-Pong :: remaining
    end.

Definition c_o_callee (network : N) :
    forall X, client_api X -> X -> Prop :=
  fun X op =>
    match op in client_api X return X -> Prop with
    | SEND _ => fun _ => exists remaining,
          serverQ network = ?-Ping :: remaining
    | WAIT => fun result =>
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
    (coh : clientQ network = !-Pong :: remaining) :
  pre (c_contract ||> C) network.
Proof.
apply: pre_to_hoare_bind=>[|? ω'];
  rewrite pre_to_hoare_triggerP // post_to_hoare_triggerP /=.
by move=>[-> _]; exists remaining.
Qed.

Lemma c_run
    (initial_network final_network : N) (p : option msg)
    (run : post (c_contract ||> C)
      initial_network p final_network) :
  p = Some Pong \/ p = None.
Proof.
move: run; rewrite post_to_hoare_bindP=> -[[] [network []]].
rewrite post_to_hoare_triggerP /= => -[-> _].
by rewrite post_to_hoare_triggerP /= => -[_].
Qed.

End client_respectful_and_run_lemmas.

End ccm.

(** ** Server Specification *)

Module scm.

Definition s_step (network : N) :
    forall X, server_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | RPLY p => send_to_client ?-p network
    | RECV => receive_from_client network
    end.

Definition s_o_caller (network : N) : forall X, server_api X -> Prop :=
  fun X op =>
    match op with
    | RPLY _ => True
    | RECV => exists remaining, serverQ network = !-Ping :: remaining
    end.

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

Lemma s_p_respect (network : N) (remaining : packets)
  (coh : serverQ network = !- Ping :: remaining) :
  pre (s_contract ||> S_p) network.
Proof.
apply: pre_to_hoare_bind=>[| [[]|] w Hpo];
  rewrite ?pre_to_hoare_triggerP //=.
- by exists remaining; exact: coh.
- move: Hpo; rewrite post_to_hoare_triggerP=> -[-> _] /= .
- apply: pre_to_hoare_bind=> [| [] w' _].
  by rewrite pre_to_hoare_triggerP.
all: exact: to_hoare_ret_preI.
Qed.

Lemma s_respect (network : N) fuel (remaining : packets)
  (coh : forall network, serverQ network = !- Ping :: remaining) :
  pre (s_contract ||> S_ fuel) network.
Proof.
move: fuel network;
  elim=> [|n ih] [/= sQ cQ] /=;
    (apply: pre_to_hoare_bind=>*; [exact/s_p_respect| ]).
- exact: to_hoare_ret_preI.
- exact: ih.
Qed.

Lemma s_p_run_grows
  (initial_network final_network : N) (result : option msg)
  (run : post (s_contract ||> S_p)
    initial_network result final_network) :
clientQ final_network = clientQ initial_network
  \/ clientQ final_network = rcons (clientQ initial_network) ?-Pong.
Proof.
move: run; rewrite post_to_hoare_bindP.
move=> [incoming [network []]];
  rewrite post_to_hoare_triggerP=> -[-> /= []] ->;
  rewrite ?post_to_hoare_triggerP ?to_hoare_ret_postE /= ?post_to_hoare_bindP
    => Hpo; [right | left];
    move: Hpo.
- case; case; case=> w; rewrite post_to_hoare_triggerP to_hoare_ret_postE;
    case=> [[-> _]].
all: by move=> [? <-];  rewrite /= client_does_not_consume_its_send.
Qed.

Lemma s_p_run_growth
    (initial_network final_network : N) (result : option msg)
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
Proof.
move: fuel initial_network final_network run;
  elim=> [|n ih] initial_network ?;
  rewrite post_to_hoare_bindP => -[ r [net [Ha ]] ];
  have [x [Hx Hg]] := s_p_run_growth Ha.
- by rewrite to_hoare_ret_postE=> -[? <-]; rewrite Hg leq_add.
by move=> H_loop; have ih' := (ih _ _ H_loop); apply: (leq_trans ih');
  rewrite Hg !addnS addnAC -addn2 ltn_add2l; exact: Hx.
Qed.

End server_respectful_and_run_lemmas.
End scm.

Import ccm scm.

(** * Protocol Description :
       +---+  == send Ping ==>  +---+  == delvr Ping ==>  +---+
       | C |                    | N |                     | S |
       +---+  <== get Pong ==   +---+  <== reply Pong ==  +---+
*)
Module ProtocolM.
Section proto_s.

Inductive proto_api : effect := one_round : proto_api outcome.

Context {ProtoF : effect} `{client_api ;; server_api -<< ProtoF}
(* `{client_api -< ProtoF, server_api -< ProtoF} *)
  {M : freerMonad ProtoF}.
Definition c : contract ProtoF N := c_contract -^- s_contract.

Local Notation "c ||> p" := (to_hoare (M:=M) c p) (at level 90).

(* Definition proto {outputF : effect} : component outputF ProtoF. *)

Definition protocol : component (M:=M) proto_api ProtoF :=
  fun _ op =>
    match op with
    | one_round =>
        send >> recv >>= fun incoming =>
          match incoming with
          | Some Ping => reply >> wait >>= fun incoming =>
            match incoming with
            | Some Pong => Ret GotPong
            | _ => Ret LostPong
            end
          | _ => Ret LostPing
          end
    end.

Definition protocol_inv (net : N) := serverQ net = [::] /\ clientQ net = [::].

(** This axiom is used here and only here because
  * the packet drop is not a question yet *)
Local Axiom WillDeliver  : forall p, ?-p = !-p.

Lemma protocol_respect (net : N) :
  protocol_inv net -> pre (c ||> protocol one_round) net.
Proof.
move=> [server_empty client_empty].
rewrite /protocol !bindA.
apply/pre_to_hoare_bind=> [|??];
  first by apply/pre_to_hoare_triggerL.
move/post_to_hoare_triggerLP=> [-> _] /=.
apply/pre_to_hoare_bind=> [|r ?].
- apply/pre_to_hoare_triggerR.
  by exists [::]; rewrite /= WillDeliver server_empty.
move/post_to_hoare_triggerRP=> [-> _].
case: r=> [[]|]; try exact: to_hoare_ret_preI.
apply/pre_to_hoare_bind=> [|??];
  first by apply/pre_to_hoare_triggerR.
move/post_to_hoare_triggerRP=> [-> _].
apply/pre_to_hoare_bind=> [|r ?].
- apply/pre_to_hoare_triggerL; exists [::].
  by rewrite /= WillDeliver client_does_not_consume_its_send client_empty.
by move/post_to_hoare_triggerLP=> [-> _];
  case: r=> [[]|]; exact: to_hoare_ret_preI.
Qed.

Lemma protocol_run_inv (n n' : N) (result : outcome) :
  protocol_inv n -> post (c |> protocol one_round) n result n' ->
   protocol_inv n'.
Proof.
move=> [server_empty client_empty].
rewrite /protocol !bindA post_to_hoare_bindP=> -[[] [? []]].
rewrite post_to_hoare_triggerLP=> -[-> _].
move/post_to_hoare_bindP=> [incoming [? []]].
rewrite post_to_hoare_triggerRP=> -[-> incoming_ok].
case: incoming_ok=> -> //=.
move/post_to_hoare_bindP=> [[] [? []]] /=;
rewrite post_to_hoare_triggerRP=> -[-> _];
move/post_to_hoare_bindP=> [wait_result [? []]].
rewrite post_to_hoare_triggerLP /=;
  case=>->;case=>->.
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
