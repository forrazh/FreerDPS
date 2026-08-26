From monae Require Import preamble hierarchy.
From mathcomp Require Import all_boot.
From FreerDPS Require Import all_freerdps ping_common hoare_correspondance.

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
Arguments S_p : simpl never.
End server_program.
End PingPongM.

Module Import Syntax.
Section syntax.
Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.

Lemma syn_send : provideLeft_isFreer (M := M) send.
Proof. by exists (frTrigger (SEND Ping)). Qed.

Lemma syn_wait : provideLeft_isFreer (M := M) wait.
Proof. by exists (frTrigger (inj $ WAIT)). Qed.

Lemma syn_c : provideLeft_isFreer (M := M) C.
Proof.
by exists (frBind (frTrigger (SEND Ping)) (fun=> frTrigger WAIT)).
Qed.

Lemma syn_reply : provideRight_isFreer (M := M) reply.
Proof. by exists (frTrigger (RPLY Pong)). Qed.

Lemma syn_recv : provideRight_isFreer (M := M) recv.
Proof. by exists (frTrigger RECV). Qed.

Lemma syn_s_p : provideRight_isFreer (M := M) S_p.
Proof.
exists
  (frBind (frTrigger RECV)
    (fun incoming =>
      if incoming is Some Ping then
        frBind (frTrigger (RPLY Pong)) (fun=> frRet incoming)
      else frRet incoming)).
rewrite /= /S_p.
congr bind.
by apply: boolp.funext=> -[[] |].
Qed.

End syntax.

#[export] Hint Extern 0 (provideLeft_isFreer send) =>
  solve [exact: syn_send] : core.
#[export] Hint Extern 0 (provideLeft_isFreer wait) =>
  solve [exact: syn_wait] : core.
#[export] Hint Extern 0 (provideLeft_isFreer C) =>
  solve [exact: syn_c] : core.
#[export] Hint Extern 0 (provideRight_isFreer reply) =>
  solve [exact: syn_reply] : core.
#[export] Hint Extern 0 (provideRight_isFreer recv) =>
  solve [exact: syn_recv] : core.
#[export] Hint Extern 0 (provideRight_isFreer S_p) =>
  solve [exact: syn_s_p] : core.

End Syntax.

Module NetworkChannelMod.

Record packet := mk_p {
  m : msg;
  can_still_be_dropped: bool
}.

Implicit Type p : packet.

Notation "!- m" := (mk_p m false) (at level 1).
Notation "?- m" := (mk_p m true) (at level 1).

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
    | WAIT => match clientQ network with
      | [::] => True
      | (!- Pong) :: _ => True
      | _ => False
      end
    (* exists remaining, clientQ network = !-Pong :: remaining *)
    end.

Definition c_o_callee (network : N) :
    forall X, client_api X -> X -> Prop :=
  fun X op =>
    match op in client_api X return X -> Prop with
    | SEND _ => fun _ => True
    | WAIT => fun result =>
                    match clientQ network with
                    | [::] => result = None
                    | !-Pong :: _ => result = Some Pong
                    | _ => False
                    end
          (* (result = Some Pong \/ result = None) *)
    end.

Definition client_c : contract client_api N :=
  make_contract c_step c_o_caller c_o_callee.


Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Fact send_respect (network : N) :
  pre (client_c ||> send) network.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact send_run (iN fN : N) (u:unit) (run : post (client_c ||> send) iN u fN ) :
  fN.(clientQ) = iN.(clientQ) /\ fN.(serverQ) = serverQ (send_to_server ?- Ping iN).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact wait_respect n (rm : packets)
    (coh : clientQ n = !-Pong :: rm \/ clientQ n = [::]) : pre (client_c ||> wait) n.
Proof.
by rewrite to_hoare_triggerE /= provided_callerP /=; case: coh=> ->.
Qed.

Fact wait_run (iN fN : N) (p: option msg) (run : post (client_c ||> wait) iN p fN ) :
  fN.(clientQ) = behead iN.(clientQ) /\ fN.(serverQ) = iN.(serverQ).
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: iN=> sQ; case=>[| [[] [] rm] ].
Qed.

Lemma c_respect
    (network : N) (remaining : packets)
    (coh : clientQ network = !-Pong :: remaining \/ clientQ network = [::]) :
  pre (client_c ||> C) network.
Proof.
apply: pre_to_hoare_bind.
- exact: send_respect.
move=> [] [sQ cQ] /send_run=> /= -[] -> -> /=.
exact/wait_respect/coh.
Qed.

Lemma c_run
    (iN fN : N) (p : option msg)
    (run : post (client_c ||> C)
      iN p fN) :
  fN.(clientQ) = behead iN.(clientQ) /\ fN.(serverQ) = serverQ (send_to_server ?- Ping iN).
Proof.
move: run.
rewrite post_to_hoare_bindP /=.
case=> [[]] [[sQ cQ]] [] /send_run [] /= -> ->.
by move/wait_run.
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
    | RECV =>
        match serverQ network with
        | [::] => True
        | (!- Ping) :: _ => True
        | _ => False
        end
    end.

Definition s_o_callee (network : N) :
    forall X, server_api X -> X -> Prop :=
  fun X op =>
    match op in server_api X return X -> Prop with
    | RECV => fun result =>
      result = None \/ result = Some Ping

    | RPLY m => fun r => match clientQ network with
        | [::] => False
        | ?-m :: _ => m = Pong
        | _ => False
        end
    end.

Definition server_c : contract server_api N :=
  make_contract s_step s_o_caller s_o_callee.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Local Notation "c ||> p" := (to_hoare (M:=M) c p)
  (at level 50, no associativity).

Fact reply_respect (network : N) :
  pre (server_c ||> reply) network.
Proof. by rewrite to_hoare_triggerE /= provided_callerP. Qed.

Fact reply_run (iN fN : N) (u:unit) (run : post (server_c ||> reply) iN u fN ) :
  fN.(clientQ) = clientQ (send_to_client ?- Pong iN) /\ fN.(serverQ) = iN.(serverQ).
Proof.
by move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
Qed.

Fact recv_respect n (rm : packets)
    (coh : serverQ n = !-Ping :: rm \/ serverQ n = [::]) : pre (server_c ||> recv) n.
Proof.
by rewrite to_hoare_triggerE /= provided_callerP /=; case: coh=> ->.
Qed.

Fact recv_run (iN fN : N) (p: option msg) (run : post (server_c ||> recv) iN p fN ) :
  fN.(clientQ) = iN.(clientQ) /\ fN.(serverQ) = behead iN.(serverQ).
Proof.
move: run; rewrite to_hoare_triggerE /= provided_calleeP /=; case=>->.
by case: iN=> + cQ; case=>[| [[] [] rm] ].
Qed.

Lemma s_p_respect (network : N) (remaining : packets)
  (coh : serverQ network = !- Ping :: remaining \/
         serverQ network = [::]) :
  pre (server_c ||> S_p) network.
Proof.
apply: pre_to_hoare_bind.
- exact/recv_respect/coh.
move=> [[]|] [sQ cQ] /recv_run=> /= -[] -> -> /=.
- apply: pre_to_hoare_bind.
  + exact: reply_respect.
  + move=>[] [s1 c1] /reply_run /= [] -> ->.
all: exact: to_hoare_ret_preI.
Qed.

Lemma s_p_run
    (iN fN : N) (result : option msg)
    (run : post (server_c ||> S_p)
      iN result fN) :
      (* this result comes from recv, thus it tells us the previous packet from the client *)
      match result with
(* success *) | Some Ping => fN.(clientQ) = clientQ (send_to_client ?- Pong iN)
(* failure *) | _         => fN.(clientQ) = clientQ iN
      end /\ fN.(serverQ) = behead iN.(serverQ) .
Proof.
move: run.
rewrite post_to_hoare_bindP.
case=>[[[]|]] [[s1 c1]] [] /recv_run /= [] -> ->.
- rewrite post_to_hoare_bindP.
case=>[[]] [[s2 c2]] [] /reply_run /= [] -> ->.
all: by rewrite to_hoare_ret_postE=> -[] <- <-.
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

Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.
Definition proto_c : contract ProtoF N := client_c -^- server_c.

(* Local Notation "c ||> p" := (to_hoare (M:=M) c p) (at level 90). *)

(* Definition S_p : M (option msg) := *)
  (* recv >>= fun inc=> if inc is Some Ping then reply >> Ret inc else Ret inc.  *)

Definition protocol : component (M:=M) proto_api ProtoF :=
  fun _ op =>
    match op with
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

Definition protocol_inv (net : N) := serverQ net = [::] /\ clientQ net = [::].

(** This axiom is used here and only here because
  * the packet drop is not a question yet *)
Local Axiom WillDeliver : forall p, ?-p = !-p.

Lemma protocol_respect (net : N) :
  protocol_inv net -> pre (proto_c |> protocol one_round) net.
Proof.
move=>[s0 c0]; rewrite /= bindA.
apply: pre_to_hoare_bind; rewrite freer_contract_left //.
- exact: send_respect.
case=> [] [s1 c1] /send_run /=.
case=> -> ->.
apply: pre_to_hoare_bind; rewrite WillDeliver s0 freer_contract_right //.
- by apply: s_p_respect; left.
move=> [[]|] [s2 c2] /s_p_run /= => -[] -> ->.
(* case: om=> [[]|]. *)
+ apply: pre_to_hoare_bind; rewrite WillDeliver c0 freer_contract_left //.
  - by apply: wait_respect=> /=; left.
move=> [[]|] [s3 c3] /wait_run => /= -[] -> ->.
all: exact: to_hoare_ret_preI.
Qed.

Lemma protocol_run_inv (n n' : N) (result : outcome) :
  protocol_inv n -> post (proto_c |> protocol one_round) n result n' ->
   protocol_inv n'.
Proof.
move=> [s0 c0]; rewrite /= bindA.
rewrite post_to_hoare_bindP freer_contract_left //; case=>[[]] [[s1 c1]] [].
move/send_run=> /= [] -> ->.
rewrite post_to_hoare_bindP freer_contract_right // s0 c0 WillDeliver;
  case=>[[[]|]] [[s2 c2]] [] /= => /s_p_run=> /= -[] -> -> .
- rewrite post_to_hoare_bindP freer_contract_left // ; case=>[inc] [[s3 c3]] [].
  move/wait_run=> /= [] -> ->; case: inc=>[[]|].
all: rewrite to_hoare_ret_postE=> -[] ? <- //.
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
