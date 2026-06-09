From monae Require Import preamble hierarchy.

(* From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct. *)
(* From infotheo Require Import realType_ext ssr_ext fsdist convex. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq.
From FreerDPS Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Obligation Tactic := simpl.

Generalizable All Variables. 
Local Open Scope monae_scope.

Create HintDb ping_db.

(**
  * We consider : 
  * - a client C (contract) ;
  * - a server S (contract) ;
  * - and a network N (lossy channel). 
  *)

(**
  * Client sends a PING packet to the server 
  * through network then waits for PONG as 
  * response.
  *)

(**
  * Server repeatedly waits for a PING packet 
  * from the network then sends a PONG as 
  * response.
  *)

(* ======================================================================== *)

(* Set of messages *)
Inductive M := ping | pong.


(* ======================================================================== *)

(* Client is described as :
 * C = send (ping); wait (pong).
 *)
Inductive client_api : interface :=
| SEND : M -> client_api unit
| WAIT : client_api M.

Definition send `{Provide ix client_api} {im : impureMonad ix} : im unit := trigger (im:=im) (inj_p $ SEND ping).
Definition wait `{Provide ix client_api} {im : impureMonad ix} : im M := trigger (im:=im) (inj_p $ WAIT).

Definition C `{Provide ix client_api} {im : impureMonad ix} : im M := send >> wait.

(* ======================================================================== *)

(* Server is described as :
 * S = μX. recv(ping); reply(pong); X.
 *)
Inductive server_api : interface :=
| RPLY : M -> server_api unit
| RECV : server_api M.

Definition reply `{Provide ix server_api} {im : impureMonad ix} : im unit := trigger (im:=im) (inj_p $ RPLY pong).
Definition recv `{Provide ix server_api} {im : impureMonad ix} : im M := trigger (im:=im) (inj_p $ RECV).

Definition S_p `{Provide ix server_api} {im : impureMonad ix} : im unit := recv >> reply.
Fixpoint S_ `{Provide ix server_api} {im : impureMonad ix} (fuel : nat) : im unit := S_p >> match fuel with | S ful => S_ (ful) | _ => skip end.

 
(* ======================================================================== *)

Check store_update.
Check make_contract.
(* store_update
     : forall s : UU0, s -> forall α : UU0, STORE s α -> α -> s *)
(* client_update
     : ChannelState -> forall α : UU0, IC α -> α -> option MessageHull *)
(* (Ω -> forall α : UU0, i α -> α -> Ω) *)
(* Definition denote_flip_effect : FlipEff ~~> fl. := 
fun X fx => match fx with 
| flip_e p => flip p
end.
 *)
(* Network is modeled as a lossy channel.  
 * N (m) = deliver (m) | drop (m)
 *)
(* Definition N := option M. *)

Module NetworkChannelMod.

Definition Id := nat.
Definition no_one : Id := 0%nat.
Record NetworkPacket : UU0 := new_packet {
  message : option M ;
  from : Id ;
  to : Id ;
  (* coh : from <> to *)
}.

Definition N := seq NetworkPacket.

Definition reply_message (om : option M) := match om with
| None => None
| Some ping => Some pong
| Some pong => Some ping
end.

Definition answer (packet : NetworkPacket) : NetworkPacket := new_packet (reply_message packet.(message)) packet.(to) packet.(from).
Definition void_packet := new_packet None no_one no_one.
(* Search list. *)

(* Fixpoint peek_last (net : N) : option NetworkPacket := match net with 
| [::] => None
| [ :: p] => Some p
| [ :: _ & ns] => peek_last ns
end.

Check last. About last. *)

Definition peek_last (net : N):= last void_packet net.

Lemma peek_empty : peek_last [::] = void_packet.
Proof. done. Qed.
  
Lemma peek_1_elem : forall p, peek_last [:: p] = p.
Proof. done. Qed. 

Lemma peek_n_elem : forall p (n np : N), rcons n p = np -> peek_last np = p.
Proof. move => ????; subst; apply/last_rcons. Qed.

Definition send_over_network (p : NetworkPacket) (net : N) : N := rcons net p.

Definition packet_contains_message (m : M) (p : NetworkPacket) : Prop := match p.(message), m with 
| None, _ => False
| Some ping, ping | Some pong, pong => True
| _, _ => False
end.

Definition last_is (m : M) (n : N) : Prop := packet_contains_message m $ peek_last n.

Fact no_packet_not_last : forall m, ~ last_is m [::].
Proof. done. Qed.

(* Search None. *)

Definition packet_not_from_me (me : Id) (p : NetworkPacket) : Prop := p.(from) <> me.

Definition last_not_from_me (me : Id) (n : N) : Prop := packet_not_from_me me $ peek_last n.



Fact size_app : forall X (n : X) (ns : seq X), size (n :: ns) = S (size ns).
Proof. done. Qed.

End NetworkChannelMod.

Import NetworkChannelMod.

(* Update function *)
(* prob update ?? *)
(* ======================================================================== *)

(* Contracts *)
      Local Open Scope nat_scope.

Module ccm.
  Section ccs.
    (* make_contract
     : forall (i : interface) (Ω : UU0),
(Ω -> forall α : UU0, i α -> α -> Ω) ->
(Ω -> forall α : UU0, i α -> Prop) ->
(Ω -> forall α : UU0, i α -> α -> Prop) -> contract i Ω *)

      Definition c_step (from to : Id) (network : N) : forall X, client_api X -> X -> N := fun X ec x =>
      match ec with
      | SEND m => send_over_network (new_packet (Some m) from to) network
      | WAIT => network
      end.

      Inductive c_o_caller (from to : Id) (st : N) : forall X, client_api X -> Prop :=
      | O_WAIT (coh : from <> to) : c_o_caller from to st WAIT
      | O_SEND (coh : from <> to) : c_o_caller from to st (SEND ping)
      .
      Hint Constructors c_o_caller : ping_db.

      Inductive c_o_callee (from to : Id) (st : N) : forall X, client_api X -> X -> Prop :=
      | WAIT_O (m : M) (msg_output : m = pong) (equ : last_not_from_me from st) : c_o_callee from to st WAIT m
      | SEND_O (u : unit) (equ : Some ping = (peek_last st).(message)) : c_o_callee from to st (SEND ping) u
      .
      Hint Constructors c_o_callee : ping_db.

      Definition c_contract (from to : Id) := make_contract (c_step from to) (c_o_caller from to) (c_o_callee from to).

      Lemma c_respect `{Provide ix client_api} {im : impureMonad ix} (you me : Id) (coh : you <> me) (network : N)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract me you) (C)) network.
      Proof.
        prove impure with ping_db;
          cleanvert o_caller0.
      Qed.

      Lemma c_run `{Provide ix client_api} {im : impureMonad ix} (you me : Id) (coh : you <> me) (initial_network final_network : N) (m : M)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract me you) (C)) initial_network m final_network)
        : size initial_network < size final_network.
      Proof.
        run_simpl run;
          cleanvert run;
          cleanvert H3;
          cleanvert H2;
          cleanvert H3;
          cleanvert H4;
          cleanvert H1;
          cleanvert equ.
        move : H2; rewrite /send_over_network/gen_witness_update/gen_callee_obligation; case (proj_p (inj_p WAIT)) => /= [e|].
        - clear H3; elim : initial_network => //=[|p ns EH] H2;
          rewrite /c_step/send_over_network; inversion H2; case e => [m' | ] //.
          + 2,3: by ssubst; move : equ; rewrite /last_not_from_me/packet_not_from_me/peek_last?last_cons?last_rcons.
      all: by rewrite ?size_rcons // size_app -PeanoNat.Nat.succ_lt_mono size_rcons.

    Qed.


  End ccs.
End ccm.

(* ------------------------------------------------------------------------ *)


Module scm.
  Section scs.


      Definition s_step (from to : Id) (network : N) : forall X, server_api X -> X -> N := fun X ec x =>
      match ec with
      | RPLY m => send_over_network (new_packet (Some m) from to) network
      | RECV => network
      end.

      Inductive s_o_caller (from to : Id) (st : N) : forall X, server_api X -> Prop :=
      | O_RECV (coh : from <> to) : s_o_caller from to st RECV
      | O_RPLY (coh : from <> to) : s_o_caller from to st (RPLY pong)
      .
      Hint Constructors s_o_caller : ping_db.

      Inductive s_o_callee (from to : Id) (st : N) : forall X, server_api X -> X -> Prop :=
      | RECV_O (m : M) (msg_output : m = ping) (equ : last_not_from_me from st) : s_o_callee from to st RECV m
      | RPLY_O (u : unit) (equ : Some pong = (peek_last st).(message)) : s_o_callee from to st (RPLY pong) u
      .
      Hint Constructors s_o_callee : ping_db.

      Definition s_contract (from to : Id) := make_contract (s_step from to) (s_o_caller from to) (s_o_callee from to).

      Lemma s_respect `{Provide ix server_api} {im : impureMonad ix} (you me : Id) (coh : you <> me) (network : N) fuel
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract me you) (S_ fuel)) network.
      Proof.
        by move : network; 
          elim : fuel => [|ful EH] network; 
          prove impure with ping_db.
      Qed.

      Lemma s_run `{Provide ix server_api} {im : impureMonad ix} (you me : Id) (coh : you <> me) (initial_network final_network : N) (u : unit) fuel
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract me you) (S_ fuel)) initial_network u final_network)
        : size initial_network < size final_network.
      Proof.
        move : run; elim : fuel => [| ful EH] run.
        run_simpl run;
          cleanvert run;
          cleanvert H3;
          cleanvert H2;
          cleanvert H3;
          cleanvert H4;
          cleanvert H1.
        move : H2 equ; elim : initial_network => [|p ns EH]; rewrite /gen_callee_obligation/gen_witness_update; case (proj_p (inj_p (RPLY pong))) => /=.
          move : equ. rewrite /gen_witness_update/last_not_from_me/packet_not_from_me/peek_last.
        move : H2; rewrite /send_over_network/gen_callee_obligation; case (proj_p (inj_p (RPLY pong))) => /= [e|].
        - elim : initial_network => //=[|p ns EH] H2;
          rewrite /s_step/send_over_network; inversion H2; case e => [m' | ] //.

          + 2,3: by ssubst; move : equ; rewrite /last_not_from_me/packet_not_from_me/peek_last?last_cons?last_rcons.
      all: by rewrite ?size_rcons // size_app -PeanoNat.Nat.succ_lt_mono size_rcons.

    Qed.

  End scs.
End scm.

(* ------------------------------------------------------------------------ *)

Import ccm scm.

(* ======================================================================== *)

(* Protocol description *)
(**
    Now, lets try to model this :

(a)    +---+ ==> (1) send ping ==> +---+ ==> (2) dlvr ping ==> +---+ 
       | C |                       | N |                       | S |
(b)    +---+ <== (4) dlvr pong <== +---+ <== (4) send pong <== +---+

**)

(* State transition system *)

(* 1 *)
Inductive ProtocolState := Init | Waiting | Done.
Inductive ProtocolTransitions : ProtocolState -> M -> ProtocolState -> Prop :=
| SendPing : ProtocolTransitions Init ping Waiting
| SendPong : ProtocolTransitions Waiting pong Done.

(* 2 *)
Inductive ProtocolStateMore := ServerWaits | ClientSent | ServerSent | ProtocolDone.
Inductive ProtocolTransitionsMore : ProtocolStateMore -> option M -> ProtocolStateMore -> Prop :=
| SendPingMore : ProtocolTransitionsMore ServerWaits (Some ping) ClientSent
| SendPongMore : ProtocolTransitionsMore ClientSent (Some pong) ServerSent
| FinishTrans : ProtocolTransitionsMore ServerSent None ProtocolDone.



(* ======================================================================== *)

(* ✨ Probability of success ✨ *)

(* A network transmission succeeds with prob `1 - p`.  *)
(* Packet loss are independant. *)

(** One single round for receiving a pong equals :
  * P(pong_recv) = P (ping_del) * P (pong_del)
  * P(pong_recv) = (1 - p) * (1 - p)
  * P(pong_recv) = (1 - p)^2
  *)

(**
  * For each retry, we get :
  * q = (1 - p)^2
  *)

(**
  * For at most n attempts, we get :
  * P(n) = 1 - (1 - q)^n = 1 - (1 
  - [1 - p]^2)^n
  *)

(** 
  * composing with quasi assoc
  * s.~ = p.~ * q.~ = p + (p.~ * q) <== this is the good equiv
  * 1 - ((1 - p) * (1 - q)) = p + ((1 - p) * q)
  * 1 - (1 - q - (p - pq)) = p + (q - pq)
  * 1 - (1 - q - p + pq) = p + q - pq
  * 1 - 1 + q + p - pq = p + q - pq
  * 0 + q + p - pq = p + q - pq
  *)