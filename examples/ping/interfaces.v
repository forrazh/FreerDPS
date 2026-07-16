From monae Require Import preamble hierarchy.
From Stdlib Require Import Lia.

From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq ssrnat.
From FreerDPS Require Import Core HoareFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Obligation Tactic := simpl.

Generalizable All Variables.
Local Open Scope monae_scope.
Import FreerFuns.

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
Inductive client_api : effect :=
| SEND : M -> client_api unit
| WAIT : client_api M.

Definition send `{Provide ix client_api} {im : freerMonad ix} : im unit :=
  trigger (im:=im) (inj_p $ SEND ping).
Definition wait `{Provide ix client_api} {im : freerMonad ix} : im M :=
  trigger (im:=im) (inj_p $ WAIT).

Definition C `{Provide ix client_api} {im : freerMonad ix} : im M :=
  send >>= fun=> wait.

(* ======================================================================== *)

Fixpoint loop `{Provide ix i} {im : freerMonad ix} (fuel : nat) `(prog : im X)
  : im unit :=
match fuel with
| 0%nat => prog >> skip
| S ful => prog >> loop ful prog
end.

(* Server is described as :
* S = μX. recv(ping); reply(pong); X.
*)
Inductive server_api : effect :=
| RPLY : M -> server_api unit
| RECV : server_api M.

Definition reply `{Provide ix server_api} {im : freerMonad ix} : im unit :=
  trigger (im:=im) (inj_p $ RPLY pong).
Definition recv `{Provide ix server_api} {im : freerMonad ix} : im M :=
  trigger (im:=im) (inj_p $ RECV).

Definition S_p `{Provide ix server_api} {im : freerMonad ix} : im unit :=
  recv >> reply.
Definition S_ `{Provide ix server_api} {im : freerMonad ix} (fuel : nat)
  : im unit :=
loop fuel S_p.


(* ======================================================================== *)

Module NetworkChannelMod.

Definition packets := seq M.

Record N := mk_chan {
  tx : packets;
  rx : packets;
}.


Definition send_over_network (m : M) (n : N) :=
  {| tx := m :: tx n; rx := rx n |}.

Definition consume_received (n : N) :=
match rx n with
| [::] => {| tx := tx n ; rx := [::] |}
| _ :: ns => {| tx := tx n ; rx := ns |}
end.

Fact consuming_has_no_effect_on_tx : forall n, tx (consume_received n) = tx n.
Proof.
  by move => n; rewrite /consume_received; case: (rx n).
Qed.

End NetworkChannelMod.

Import NetworkChannelMod.

(* ======================================================================== *)

(* Contracts *)
Local Open Scope nat_scope.

Module ccm.
Section ccs.
(* make_contract
: forall (i : effect) (Ω : UU0),
(Ω -> forall α : UU0, i α -> α -> Ω) ->
(Ω -> forall α : UU0, i α -> Prop) ->
(Ω -> forall α : UU0, i α -> α -> Prop) -> contract i Ω *)

Definition c_step (network : N) : forall X, client_api X -> X -> N :=
fun X ec x =>
match ec with
| SEND m => send_over_network m network
  (* add packet tx *)
| WAIT => consume_received network
  (* remove packet rx (if present) *)
end.

Inductive c_o_caller (st : N) : forall X, client_api X -> Prop :=
| O_WAIT (equ : forall ns, ping :: ns = st.(tx)) : c_o_caller st WAIT
| O_SEND (m : M) : c_o_caller st (SEND m)
.

Inductive c_o_callee (st : N) : forall X, client_api X -> X -> Prop :=
| SEND_O (u : unit) (m : M) (equ_m : m = ping)
  (equ : forall ns, m :: ns = st.(tx)) : c_o_callee st (SEND m) u
| WAIT_O : c_o_callee st WAIT pong.

Definition c_contract :=
make_contract c_step no_caller_obligation c_o_callee.

(* Safety *)
Lemma c_respect `{Provide ix client_api} {im : freerMonad ix} (network : N)
  : pre (to_hoare (im:=im) c_contract C) network.
Proof.
by apply/to_hoare_bind_preI=> [|??];
  rewrite to_hoare_request_preE /gen_caller_obligation proj_inj_p_equ.
Qed.

(* Liveness *)
Lemma wait_postE `{Provide ix client_api} (network final_network : N) (m : M) :
  post (to_hoare (im:=freer ix) c_contract wait) network m final_network ->
  m = pong.
Proof.
rewrite to_hoare_request_postE /gen_witness_update /gen_callee_obligation !proj_inj_p_equ /=.
by move=> [_ wait]; inversion wait; ssubst.
Qed.

Lemma c_run `{Provide ix client_api} {im : freerMonad ix} (initial_network final_network : N) (m : M)
    (run : post (to_hoare (im:=freer ix) c_contract C) initial_network m final_network)
  : m = pong.
Proof.
move: run; rewrite to_hoare_bind_postE.
by move=> -[? [? [_ +]]]=> /wait_postE.
Qed.

End ccs.
End ccm.

(* ------------------------------------------------------------------------ *)


Module scm.
Section scs.


Definition s_step (network : N) : forall X, server_api X -> X -> N :=
fun X ec x =>
match ec with
| RPLY m => send_over_network m network
| RECV => consume_received network
end.

Inductive s_o_caller (st : N) : forall X, server_api X -> Prop :=
| O_RECV (*blocking : rx st <> [::]*) : s_o_caller st RECV
| O_RPLY (m : M) : s_o_caller st (RPLY m)
.
Hint Constructors s_o_caller : ping_db.

Inductive s_o_callee (st : N) : forall X, server_api X -> X -> Prop :=
| RECV_O (m : M) : s_o_callee st RECV ping
| RPLY_O (u : unit) (m : M) : s_o_callee st (RPLY m) u
.
Hint Constructors s_o_callee : ping_db.

Definition s_contract := make_contract s_step s_o_caller s_o_callee.

Lemma recv_postE `{Provide ix server_api} {im : freerMonad ix}
    (network final_network : N) (m : M) :
  post (to_hoare (im:=im) s_contract recv) network m final_network ->
  m = ping /\ final_network = consume_received network.
Proof.
rewrite /recv to_hoare_request_postE /gen_witness_update.
rewrite /gen_callee_obligation proj_inj_p_equ /=.
move=> [-> recv_result].
inversion recv_result; ssubst.
by [].
Qed.

Lemma reply_postE `{Provide ix server_api} {im : freerMonad ix}
    (network final_network : N) (u : unit) :
  post (to_hoare (im:=im) s_contract reply) network u final_network ->
  final_network = send_over_network pong network.
Proof.
rewrite /reply to_hoare_request_postE /gen_witness_update.
rewrite /gen_callee_obligation proj_inj_p_equ /=.
by move=> [-> _].
Qed.

Import SpecializedHoareModule.

Lemma s_p_respect `{Provide ix server_api} {im : freerMonad ix}
    (network : N) :
  pre (to_hoare (im:=im) s_contract S_p) network.
Proof.
by apply/to_hoare_bind_preI=> [|??];
  rewrite to_hoare_request_preE /gen_caller_obligation proj_inj_p_equ;
  constructor.
Qed.

Lemma s_respect `{Provide ix server_api}
(network : N) fuel
: pre (to_hoare (im:=freer ix) s_contract (S_ fuel)) network.
Proof.
move: network; elim: fuel=> [|n ih] network;
  apply/to_hoare_bind_preI=> [|??].
- exact/s_p_respect.
- by move=>_; apply/to_hoare_skip_preI.
- exact/s_p_respect.
- by move=>?; apply/ih.
Qed.

Lemma s_p_run_grows `{Provide ix server_api} {im : freerMonad ix}
(initial_network final_network : N) (u : unit)
(run : post (to_hoare (im:=im) s_contract S_p)
initial_network u final_network)
: tx final_network = pong :: tx initial_network.
Proof.
move: run; rewrite to_hoare_bind_postE=> -[received [net [recv_run reply_run]]].
move: reply_run recv_run
  => /reply_postE ->
  => /recv_postE [_ ->].
by rewrite /= consuming_has_no_effect_on_tx.
Qed.

Lemma s_run `{Provide ix server_api}
(initial_network final_network : N) (u : unit) fuel
(run : post (to_hoare (im:=freer ix) s_contract (S_ fuel))
initial_network u final_network)
: tx final_network = nseq (S fuel) pong ++ tx initial_network.
Proof.
move: initial_network final_network u run.
elim: fuel=> [|fuel IH] initial_network final_network u run.
- move: run.
  rewrite /S_ /loop to_hoare_bind_postE.
  move=> [x [middle_network [run_p run_skip]]].
  move: run_skip.
  rewrite to_hoare_local_postE=> -[_ <-].
  by rewrite /= (s_p_run_grows run_p).
move: run.
rewrite /S_ /loop to_hoare_bind_postE.
move=> [x [middle_network [run_p run_loop]]].
rewrite (IH _ _ _ run_loop) (s_p_run_grows run_p).
have nseq_pong_cons : forall n,
  nseq n pong ++ pong :: tx initial_network =
  nseq (S n) pong ++ tx initial_network.
  by elim=> [|n IHn] //=; rewrite IHn.
exact: nseq_pong_cons.
Qed.

Lemma s_run_size `{Provide ix server_api}
(initial_network final_network : N) (u : unit) fuel
(run : post (to_hoare (im:=freer ix) s_contract (S_ fuel))
initial_network u final_network)
: size (tx final_network) = size (tx initial_network) + fuel + 1.
Proof.
by rewrite (s_run run) size_cat size_nseq addSn addnC addn1.
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
