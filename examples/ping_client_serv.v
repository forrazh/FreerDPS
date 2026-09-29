From monae Require Import preamble hierarchy.
From mathcomp Require Import boot.
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
  | O => program >> skip
  | S remaining => program >> loop remaining program
  end.
Definition S_ (fuel : nat) : M unit := loop fuel S_p.
Arguments S_p : simpl never.
End server_program.
End PingPongM.

Module Export PingSyntax.
Section syntax.
Context {ProtoF : effect} {Hc: client_api -< ProtoF} {Hs: server_api -< ProtoF}.
Context {M : freerMonad ProtoF}.
Lemma syn_send : providesOnlyF (H:=Hc) (M := M) send.
Proof. by exists (frTrigger (SEND Ping)). Qed.

Lemma syn_wait : providesOnlyF (H:=Hc) (M := M) wait.
Proof. by exists (frTrigger (inj $ WAIT)). Qed.

Lemma syn_c : providesOnlyF (F:=client_api) (M := M) C.
Proof.
by exists (frBind (frTrigger (SEND Ping)) (fun=> frTrigger WAIT)).
Qed.

Lemma syn_reply : providesOnlyF (F:=server_api) (M := M) reply.
Proof. by exists (frTrigger (RPLY Pong)). Qed.

Lemma syn_recv : providesOnlyF (F:=server_api) (M := M) recv.
Proof. by exists (frTrigger RECV). Qed.

Lemma syn_s_p : providesOnlyF (F:=server_api) (M := M) S_p.
Proof.
exists
  (frBind (frTrigger RECV)
    (fun incoming =>
      if incoming is Some Ping then
        frBind (frTrigger (RPLY Pong)) (fun=> frRet incoming)
      else frRet incoming)).
rewrite /= /S_p.
congr (recv >>= _).
by apply: boolp.funext=> -[[] |].
Qed.
End syntax.

#[export] Hint Extern 0 (providesOnlyF send) =>
  solve [exact: syn_send] : core.
#[export] Hint Extern 0 (providesOnlyF wait) =>
  solve [exact: syn_wait] : core.
#[export] Hint Extern 0 (providesOnlyF C) =>
  solve [exact: syn_c] : core.
#[export] Hint Extern 0 (providesOnlyF reply) =>
  solve [exact: syn_reply] : core.
#[export] Hint Extern 0 (providesOnlyF recv) =>
  solve [exact: syn_recv] : core.
#[export] Hint Extern 0 (providesOnlyF S_p) =>
  solve [exact: syn_s_p] : core.

End PingSyntax.

Module NetworkChannelMod.

Definition packet := option msg.

Record net_state := mk_chan {
  serverQ : packet;
  clientQ : packet;
}.
Implicit Type p : packet.
Implicit Type ns : net_state.
Implicit Type m : msg.

Definition fill_serverQ m ns :=
  {| serverQ := Some m;
     clientQ := clientQ ns |}.

Definition fill_clientQ m ns :=
  {| serverQ := serverQ ns;
     clientQ := Some m |}.

Definition consume_clientQ ns :=
  match clientQ ns with
  | None => ns
  | Some _ =>
      {| serverQ := serverQ ns;
         clientQ := None |}
  end.

Definition consume_serverQ ns :=
  match serverQ ns with
  | None => ns
  | Some _ =>
      {| serverQ := None;
         clientQ := clientQ ns |}
  end.

Lemma server_does_not_consume_its_send ns :
  serverQ (consume_clientQ ns) = serverQ ns.
Proof. by rewrite /consume_clientQ; case: (clientQ ns). Qed.

Lemma client_does_not_consume_its_send ns :
  clientQ (consume_serverQ ns) = clientQ ns.
Proof. by rewrite /consume_serverQ; case: (serverQ ns). Qed.

Definition drop_last (ps : packet) (keep:bool) := match ps with
| None => None
| Some _ => if keep then ps else None
end.

Definition drop_from_serv ns (keep : bool) := match ns with
| mk_chan srvQ cliQ => {|serverQ:= drop_last srvQ keep; clientQ:= cliQ|}
end.

Definition drop_from_cli ns (keep : bool) := match ns  with
| mk_chan srvQ cliQ => {|serverQ:= srvQ; clientQ:= drop_last cliQ keep|}
end.

Definition drop_new_packet ns (keep: bool) (q: bool) :=
if q then drop_from_serv ns keep
else drop_from_cli ns keep.

End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

(** ** Client Specification *)

Module ccm.

Definition c_step ns :
    forall X, client_api X -> X -> net_state :=
  fun X cmd result => match cmd with
    | SEND p => fill_serverQ p ns
    | WAIT => consume_clientQ ns
    end.

Definition client_req ns : forall X, client_api X -> bool :=
  fun X cmd => match cmd with
    | SEND _ => true
    | WAIT => clientQ ns != Some Ping
    end.

Definition client_promise ns :
    forall X, client_api X -> X -> bool :=
  fun X cmd =>
    match cmd with
    | SEND _ => fun _ => serverQ ns == Some Ping
    | WAIT => fun result => result != Some Ping
    end.

Definition client_c : contract client_api net_state :=
  make_contract c_step client_req client_promise.


Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Fact send_respect ns :
  pre (client_c |> (send : M _)) ns.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact send_run (ins fns : net_state) (u:unit) (run : post (client_c |> (send : M _)) ins u fns ) :
  fns.(clientQ) = ins.(clientQ)
  /\ fns.(serverQ) = serverQ (fill_serverQ Ping ins).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact wait_respect n (coh : clientQ n != Some Ping) : pre (client_c |> (wait : M _)) n.
Proof.
Proof. by rewrite to_hoare_triggerE /= provided_callerP /=. Qed.

Fact wait_run (ins fns : net_state) p (run : post (client_c |> (wait : M _)) ins p fns ) :
  fns.(clientQ) = None /\ fns.(serverQ) = ins.(serverQ).
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: ins=> sQ; case.
Qed.

Lemma c_respect ns
    (coh : clientQ ns != Some Ping) :
  pre (client_c |> (C : M _)) ns.
Proof.
rewrite freer_to_hoare_bindE; split.
- exact: send_respect.
move=> [] [sQ cQ] /send_run=> /= -[] -> -> /=.
exact/wait_respect/coh.
Qed.

Lemma c_run
    (ins fns : net_state) (p : option msg)
    (run : post (client_c |> (C : M _)) ins p fns) :
  fns.(clientQ) = None /\ fns.(serverQ) = serverQ (fill_serverQ Ping ins).
Proof.
move: run.
rewrite freer_to_hoare_bindE.
case=> [[]] [[sQ cQ]] [] /send_run [] /= -> ->.
by move/wait_run.
Qed.

End client_respectful_and_run_lemmas.

End ccm.

(** ** Server Specification *)

Module scm.

Definition server_step ns :
    forall X, server_api X -> X -> net_state :=
  fun X cmd result => match cmd with
| RPLY p => fill_clientQ p ns
| RECV => consume_serverQ ns
end.

Definition server_req ns : forall X, server_api X -> bool :=
  fun X cmd => match cmd with
| RPLY _ => true
| RECV => serverQ ns != Some Pong
end.

Definition server_promise ns :
    forall X, server_api X -> X -> bool := fun X cmd =>
match cmd with
| RECV => fun result => result != Some Pong
| RPLY m => fun _ => clientQ ns == Some Pong
end.

Definition server_c : contract server_api net_state :=
  make_contract server_step server_req server_promise.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Fact reply_respect ns :
  pre (server_c |> (reply : M _)) ns.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact reply_run (ins fns : net_state) (u : unit)
    (run : post (server_c |> (reply : M _)) ins u fns) :
  fns.(clientQ) = clientQ (fill_clientQ Pong ins) /\
  fns.(serverQ) = ins.(serverQ).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact recv_respect n (coh : serverQ n != Some Pong) :
 (* = Some Ping \/ serverQ n = None) : *)
  pre (server_c |> (recv : M _)) n.
Proof. by rewrite to_hoare_triggerE /= provided_callerP /=. Qed.

Fact recv_run (ins fns : net_state) (p : option msg)
    (run : post (server_c |> (recv : M _)) ins p fns) :
  fns.(clientQ) = ins.(clientQ) /\ fns.(serverQ) = None.
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: ins; case.
Qed.

Lemma s_p_respect ns (coh : serverQ ns != Some Pong) :
 (* !- Ping \/ serverQ ns = None) : *)
  pre (server_c |> (S_p : M _)) ns.
(* Proof. *)
rewrite /S_p freer_to_hoare_bindE; split.
  exact/recv_respect/coh.
move=> [[]|] [sQ cQ] /recv_run=> /= -[] -> -> /=.
- rewrite freer_to_hoare_bindE; split.
    exact: reply_respect.
  move=> *.
all: by rewrite pre_ret.
Qed.

Lemma s_p_run
    (ins fns : net_state) (result : option msg)
    (run : post (server_c |> (S_p : M _)) ins result fns) :
  match result with
  | Some Ping => fns.(clientQ) = clientQ (fill_clientQ Pong ins)
  | _ => fns.(clientQ) = clientQ ins
  end /\ fns.(serverQ) = None.
Proof.
move: run; rewrite freer_to_hoare_bindE.
case=>[[[]|]] [[s1 c1]] [] /recv_run /= [] -> ->.
- rewrite freer_to_hoare_bindE.
  case=>[[]] [[s2 c2]] [] /reply_run /= [] -> ->.
all: by rewrite post_ret; case=> <- <-.
Qed.

End server_respectful_and_run_lemmas.
End scm.

Import ccm scm.

(** * Protocol Description :
       +---+  == send Ping ==>  +-----------+  == delvr Ping ==>  +---+
       | C |                    | net_state |                     | S |
       +---+  <== get Pong ==   +-----------+  <== reply Pong ==  +---+
*)
Module ProtocolM.
Section proto_s.

Inductive ping_round : effect := one_round : ping_round outcome.

Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.

Definition ping_protocol : component (M:=M) ping_round ProtoF :=
  fun _ cmd => match cmd with
    | one_round =>
        send >> S_p >>= fun om => match om with
          | Some Ping => wait >>= fun om =>
            if om is Some Pong then Ret GotPong else Ret LostPong
          | _ => Ret LostPing
          end
    end.

Definition ping_contract : contract ProtoF net_state := client_c -^- server_c.
Definition ping_inv (net : net_state) := serverQ net = None /\ clientQ net = None.

Lemma pre_ping (net : net_state) :
  ping_inv net -> pre (ping_contract |> ping_protocol one_round) net.
Proof.
move=>[s0 c0]; rewrite /= bindA.
rewrite freer_to_hoare_bindE freer_contract_left //=; split.
  exact: send_respect.
case=> [] [s1 c1] /send_run /=.
case=> -> ->.
rewrite freer_to_hoare_bindE freer_contract_right //; split.
  exact/s_p_respect/eqP.
move=> [[]|] [s2 c2] /s_p_run /= => -[] -> ->.
+ rewrite freer_to_hoare_bindE freer_contract_left //=; split.
    exact/wait_respect/eqP.
move=> [[]|] [s3 c3] /wait_run => /= -[] -> ->.
all: by rewrite pre_ret.
Qed.

Lemma post_ping (n n' : net_state) (result : outcome) :
  ping_inv n -> post (ping_contract |> ping_protocol one_round) n result n' ->
   ping_inv n'.
Proof.
move=> [s0 c0]; rewrite /= bindA.
rewrite freer_to_hoare_bindE.
rewrite freer_contract_left //;
  case=>[[]] [[s1 c1]] [].
move/send_run=> /= [] -> ->.
rewrite freer_to_hoare_bindE freer_contract_right //;
  case=>[[[]|]] [[s2 c2]] [] /= => /s_p_run=> /= -[] -> -> .
- rewrite freer_to_hoare_bindE freer_contract_left //;
    case=>[inc] [[s3 c3]] [].
  move/wait_run=> /= [] -> ->; case: inc=>[[]|].
all: by rewrite post_ret=> -[] ? <- //.
Qed.

Theorem ping_correct :
  correct_component ping_protocol (no_contract ping_round) ping_contract
    (fun=> ping_inv).
Proof.
move=>[] n inv ? [] []; split=>[|m n' Hpost] /=.
  exact: pre_ping.
by split=>//; move: (post_ping inv Hpost).
Qed.

End proto_s.
End ProtocolM.

(** * Probability of Success *)

(******************************************************************************)
(* TODO: Rewrite the above using FlipEff instead of `ping_round`, normally the *)
(*       proofs should be quite straightforward (reusing ping_freer_prob.v at *)
(*       most points).                                                        *)
(******************************************************************************)

(**
A ns transmission succeeds with probability [1 - p]. Packet losses are
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

