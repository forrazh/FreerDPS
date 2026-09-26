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



Notation "!- m" := (Some m) (at level 1).
(* Notation "?- m" := (None) (at level 1). *)

(* Definition packets := seq packet. *)

Record net_state := mk_chan {
  serverQ : packet;
  clientQ : packet;
}.
Implicit Type p : packet.
Implicit Type ns : net_state.
Implicit Type m : msg.

(* Definition enqueue p (queue : packets) :=
  rcons queue p. *)

Definition send_to_server m ns :=
  {| serverQ := Some m;
     clientQ := clientQ ns |}.

Definition send_to_client m ns :=
  {| serverQ := serverQ ns;
     clientQ := Some m |}.

Definition receive_from_server ns :=
  match clientQ ns with
  | None => ns
  | Some _ =>
      {| serverQ := serverQ ns;
         clientQ := None |}
  end.

Definition receive_from_client ns :=
  match serverQ ns with
  | None => ns
  | Some _ =>
      {| serverQ := None;
         clientQ := clientQ ns |}
  end.

Lemma server_does_not_consume_its_send ns :
  serverQ (receive_from_server ns) = serverQ ns.
Proof. by rewrite /receive_from_server; case: (clientQ ns). Qed.

Lemma client_does_not_consume_its_send ns :
  clientQ (receive_from_client ns) = clientQ ns.
Proof. by rewrite /receive_from_client; case: (serverQ ns). Qed.

(* Definition deliver p := match p with
| mk_p m _ => !-m
end.
Notation "!!- x" := (deliver x) (at level 1). *)


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
  fun X cmd result =>
    match cmd with
    | SEND p => send_to_server p ns
    | WAIT => receive_from_server ns
    end.

Definition c_requirment ns : forall X, client_api X -> Prop :=
  fun X cmd =>
    match cmd with
    | SEND _ => True
    | WAIT => match clientQ ns with
      | Some Ping => False
      | _ => True
      end
    (* exists remaining, clientQ ns = !-Pong :: remaining *)
    end.

Definition c_promise ns :
    forall X, client_api X -> X -> Prop :=
  fun X cmd =>
    match cmd in client_api X return X -> Prop with
    | SEND _ => fun _ => True
    | WAIT => fun result =>
                    match clientQ ns with
                    | None => result = None
                    | Some Pong => result = Some Pong
                    | _ => False
                    end
          (* (result = Some Pong \/ result = None) *)
    end.

Definition client_c : contract client_api net_state :=
  make_contract c_step c_requirment c_promise.


Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Fact send_respect ns :
  pre (client_c |> (send : M _)) ns.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact send_run (ins fns : net_state) (u:unit) (run : post (client_c |> (send : M _)) ins u fns ) :
  fns.(clientQ) = ins.(clientQ)
  /\ fns.(serverQ) = serverQ (send_to_server Ping ins).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact wait_respect n
    (coh : clientQ n = Some Pong \/ clientQ n = None) : pre (client_c |> (wait : M _)) n.
Proof.
by rewrite to_hoare_triggerE /= provided_callerP /=; case: coh=> ->.
Qed.

Fact wait_run (ins fns : net_state) p (run : post (client_c |> (wait : M _)) ins p fns ) :
  fns.(clientQ) = None /\ fns.(serverQ) = ins.(serverQ).
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: ins=> sQ; case.
Qed.

Lemma c_respect ns
    (coh : clientQ ns = Some Pong \/ clientQ ns = None) :
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
  fns.(clientQ) = None /\ fns.(serverQ) = serverQ (send_to_server Ping ins).
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

Definition s_step ns :
    forall X, server_api X -> X -> net_state := fun X cmd result =>
match cmd with
| RPLY p => send_to_client p ns
| RECV => receive_from_client ns
end.

Definition s_requirement ns : forall X, server_api X -> Prop :=
  fun X cmd =>
match cmd with
| RPLY _ => True
| RECV => match serverQ ns with
          | Some Pong => False
          | _ => True
          end
end.

Definition s_promise ns :
    forall X, server_api X -> X -> Prop := fun X cmd =>
match cmd with
| RECV => fun result => result = None \/ result = Some Ping
| RPLY m => fun r => match clientQ ns with
                      | None => False
                      | Some m => m = Pong
                      end
end.


Definition server_c : contract server_api net_state :=
  make_contract s_step s_requirement s_promise.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Fact reply_respect ns :
  pre (server_c |> (reply : M _)) ns.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact reply_run (ins fns : net_state) (u : unit)
    (run : post (server_c |> (reply : M _)) ins u fns) :
  fns.(clientQ) = clientQ (send_to_client Pong ins) /\
  fns.(serverQ) = ins.(serverQ).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact recv_respect n (coh : serverQ n = !-Ping \/ serverQ n = None) :
  pre (server_c |> (recv : M _)) n.
Proof.
by rewrite to_hoare_triggerE /= provided_callerP /=; case: coh=> ->.
Qed.

Fact recv_run (ins fns : net_state) (p : option msg)
    (run : post (server_c |> (recv : M _)) ins p fns) :
  fns.(clientQ) = ins.(clientQ) /\ fns.(serverQ) = None.
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: ins; case.
Qed.

Lemma s_p_respect ns (coh : serverQ ns = !- Ping \/ serverQ ns = None) :
  pre (server_c |> (S_p : M _)) ns.
Proof.
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
  | Some Ping => fns.(clientQ) = clientQ (send_to_client Pong ins)
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

Inductive proto_api : effect := one_round : proto_api outcome.

Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.

Definition protocol : component (M:=M) proto_api ProtoF :=
  fun _ cmd =>
    match cmd with
    | one_round =>
        send >> S_p >>= fun inc => match inc with
          | Some Ping => wait >>= fun inc =>
            match inc with
            | Some Pong => Ret GotPong
            | _ => Ret LostPong
            end
          | _ => Ret LostPing
          end
    end.

Definition proto_c : contract ProtoF net_state := client_c -^- server_c.
Definition protocol_inv (net : net_state) := serverQ net = None /\ clientQ net = None.
(** This axiom is used here and only here because
  * the packet drop is not a question yet *)
(* Local Axiom WillDeliver : forall p, ?-p = !-p. *)

Lemma protocol_respect (net : net_state) :
  protocol_inv net -> pre (proto_c |> protocol one_round) net.
Proof.
move=>[s0 c0]; rewrite /= bindA.
rewrite freer_to_hoare_bindE freer_contract_left //=; split.
  exact: send_respect.
case=> [] [s1 c1] /send_run /=.
case=> -> ->.
rewrite freer_to_hoare_bindE freer_contract_right //; split.
  by apply: s_p_respect; left.
move=> [[]|] [s2 c2] /s_p_run /= => -[] -> ->.
+ rewrite freer_to_hoare_bindE freer_contract_left //=; split.
    by apply: wait_respect=> /=; left.
move=> [[]|] [s3 c3] /wait_run => /= -[] -> ->.
all: by rewrite pre_ret.
Qed.

Lemma protocol_run_inv (n n' : net_state) (result : outcome) :
  protocol_inv n -> post (proto_c |> protocol one_round) n result n' ->
   protocol_inv n'.
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

Lemma proto_correct :
  correct_component protocol (no_contract proto_api) proto_c
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


