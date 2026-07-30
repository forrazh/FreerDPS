From monae Require Import preamble hierarchy.
From mathcomp Require Import all_boot.
From FreerDPS Require Import Core.

Import FreerFuns.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(** * Specifying the Ping-Pong Protocol *)

Module Export PingPongM.

(** ** Messages *)

Inductive Msg := ping | pong.

(** ** Client *)

Inductive client_api : effect :=
| SEND : Msg -> client_api unit
| WAIT : client_api Msg.

Section client_program.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Definition send : M unit := trigger $ SEND ping.
Definition wait : M Msg := trigger WAIT.
Definition C : M Msg :=
  send >>= fun=> wait.
End client_program.

(** ** Server *)

Inductive server_api : effect :=
| RPLY : Msg -> server_api unit
| RECV : server_api Msg.

Section server_program.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Definition reply : M unit := trigger $ RPLY pong.
Definition recv : M Msg := trigger RECV.
Definition S_p : M unit := recv >> reply.
Fixpoint loop {X : Type} (fuel : nat) (program : M X) : M unit :=
  match fuel with
  | 0%nat => program >> skip
  | S remaining => program >> loop remaining program
  end.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.
End server_program.
End PingPongM.

Module NetworkChannelMod.

Definition packets := seq Msg.

Record N := mk_chan {
  tx : packets;
  rx : packets;
}.

Definition send_over_network (message : Msg) (network : N) :=
  {| tx := message :: tx network; rx := rx network |}.

Definition consume_received (network : N) :=
  match rx network with
  | [::] => {| tx := tx network; rx := [::] |}
  | _ :: remaining => {| tx := tx network; rx := remaining |}
  end.

Lemma consuming_has_no_effect_on_tx network :
  tx (consume_received network) = tx network.
Proof. by rewrite /consume_received; case : (rx network). Qed.

End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

(** ** Client Specification *)

Module ccm.

Definition c_step (network : N) :
    forall X, client_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | SEND message => send_over_network message network
    | WAIT => consume_received network
    end.

Inductive c_o_caller (network : N) :
    forall X, client_api X -> Prop :=
| O_WAIT (remaining : packets)
    (pong_available : rx network = pong :: remaining) :
    c_o_caller network WAIT
| O_SEND (message : Msg) : c_o_caller network (SEND message).

Inductive c_o_callee (network : N) :
    forall X, client_api X -> X -> Prop :=
| SEND_O (message : Msg) (result : unit) :
    c_o_callee network (SEND message) result
| WAIT_O (remaining : packets)
    (received_pong : rx network = pong :: remaining) :
    c_o_callee network WAIT pong.

Definition c_contract : contract client_api N :=
  make_contract c_step c_o_caller c_o_callee.


Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma c_respect
    (network : N) (remaining : packets)
    (pong_available : rx network = pong :: remaining) :
  pre (c_contract ||> C) network.
Proof.
apply: th_pre_bindA=>*; rewrite to_hoare_trigger_preE /=.
- constructor.
admit.
(* Equational bind reasoning; proj_inj for [SEND] and [WAIT]. *)
Admitted.

Lemma c_run
    (initial_network final_network : N) (message : Msg)
    (run : post (c_contract ||> C)
      initial_network message final_network) :
  message = pong.
Proof.
by move: run;
  rewrite th_post_bindA=>-[?[n []]];
  do 2 (rewrite to_hoare_trigger_postE /= => [ [?] ];
    inversion 1; ssubst).
Qed.

End client_respectful_and_run_lemmas.

End ccm.

(** ** Server Specification *)

Module scm.

Definition s_step (network : N) :
    forall X, server_api X -> X -> N :=
  fun X operation result =>
    match operation with
    | RPLY message => send_over_network message network
    | RECV => consume_received network
    end.

Inductive s_o_caller (network : N) :
    forall X, server_api X -> Prop :=
| O_RECV : s_o_caller network RECV
| O_RPLY (message : Msg) : s_o_caller network (RPLY message).

Inductive s_o_callee (network : N) :
    forall X, server_api X -> X -> Prop :=
| RECV_O (message : Msg) : s_o_callee network RECV ping
| RPLY_O (result : unit) (message : Msg) :
    s_o_callee network (RPLY message) result.

Definition s_contract : contract server_api N :=
  make_contract s_step s_o_caller s_o_callee.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Lemma s_p_respect (network : N) :
  pre (s_contract ||> S_p) network.
Proof.
by apply: th_pre_bindA=>*; rewrite to_hoare_trigger_preE /=; constructor.
Qed.

Lemma s_respect (network : N) fuel :
  pre (s_contract ||> S_ fuel) network.
Proof.
move: fuel network;
  elim=> [|n ih] ?;
    (apply: th_pre_bindA=>*; [exact: s_p_respect| ]).
- exact: to_hoare_skip_preI.
- exact: ih.
Qed.

Lemma s_p_run_grows
    (initial_network final_network : N) (result : unit)
    (run : post (s_contract ||> S_p)
      initial_network result final_network) :
  tx final_network = pong :: tx initial_network.
Proof.
move: run; rewrite th_post_bindA=>[ [? [? [ ]]] ].
do 2 (rewrite to_hoare_trigger_postE /= => [ [?] ];
  inversion 1; ssubst).
by rewrite /= consuming_has_no_effect_on_tx.
Qed.

Lemma s_run
    (initial_network final_network : N) (result : unit) fuel
    (run : post (s_contract ||> S_ fuel)
      initial_network result final_network) :
  tx final_network =
    nseq (S fuel) pong ++ tx initial_network.
Proof.
move: fuel initial_network final_network run;
  elim=> [|n ih] initial_network ?;
  rewrite th_post_bindA=> -[ [] [net [H_s +]] ].
- by rewrite to_hoare_skip_postE /==> -[? <-]; exact: s_p_run_grows H_s.
move=> H_loop; rewrite (ih _ _ H_loop) (s_p_run_grows H_s).
by elim n => //= [? ->] //.
Qed.

Lemma s_run_size
    (initial_network final_network : N) (result : unit) fuel
    (run : post (s_contract ||> S_ fuel)
      initial_network result final_network) :
  size (tx final_network) =
    size (tx initial_network) + fuel + 1.
Proof.
by rewrite (s_run run) size_cat size_nseq addSn addnC addn1.
Qed.

End server_respectful_and_run_lemmas.

End scm.

Import ccm scm.

(** * Protocol Description *)

(**

<<
       +---+  == send ping ==>  +---+  == deliver ping ==>  +---+
       | C |                    | N |                        | S |
       +---+  <== get pong ==   +---+  <== reply pong =====  +---+
>>

*)

(** * Probability of Success *)

(**
A network transmission succeeds with probability [1 - p]. Packet losses are
independent. For one round trip:

<<
P(pong received) = P(ping delivered) * P(pong delivered)
                 = (1 - p) * (1 - p)
                 = (1 - p)^2.
>>

For at most [n] attempts, with [q = (1 - p)^2]:

<<
P(n) = 1 - (1 - q)^n.
>>
*)
