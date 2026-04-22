(* Definition interface : Type := Type -> Type. *)
From FreerDPS Require Import Core Impure ProbInterface.
From monae Require Import preamble hierarchy.

From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct.
From infotheo Require Import realType_ext ssr_ext fsdist convex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Obligation Tactic := idtac.

Local Open Scope monae_scope.

Create HintDb ping_p.


(* +++ Protocole +++ *)
Inductive Msg := 
| Ping : Msg
| Pong : Msg.

Definition Ωc : UU0 := option Msg.
Definition Ωs : UU0 := option Msg.
Definition Ω : UU0 := Ωc * Ωs.


Inductive PingState := Init | ClientSent | ServerAnswered.

Inductive PingTransition : PingState -> Msg -> PingState -> Prop :=
| t_ping : PingTransition Init Ping ClientSent
| t_pong : PingTransition ClientSent Pong ServerAnswered
.

(* Inductive trace *)


(* ------------ *)

(* +++ Architecture +++ *)

Definition Id := nat.

Inductive PingClient : interface :=
| SendEC : Id -> Msg -> PingClient unit
| ReceiveEC : Id -> PingClient Msg.

Inductive PingServer : interface :=
| ReceiveES : PingServer Id
| SendES : Id -> Msg -> PingServer unit.

Definition is_some : forall A, option A -> Prop := fun _ x => match x with | Some _ => True | None => False end .

Definition ping_witness_update (ω : Ω) (α : UU0) (e : PingClient α) (a : α) : Ω := 
match e with 
| SendEC i m => (Some Ping, snd ω)
| ReceiveEC i => (None, snd ω)
end. 

Inductive o_caller_ping_client (ω : Ω) : forall (α : Type), PingClient α -> Prop :=
(* Given the id [i] of a system [ω], a ping message message can always get sent *)
| client_send_ocaller (i : Id) : o_caller_ping_client ω (SendEC i Ping)
(* Given the id [i] of a system [ω], if a ping message was sent before hand, you should have received a Pong *)
| client_recv_ocaller (i : Id) (equ : fst ω = Some Ping -> snd ω = Some Pong) : o_caller_ping_client ω (ReceiveEC i).

Hint Constructors o_caller_ping_client : ping_p.

Inductive o_callee_ping_client (ω : Ω) : forall (α : Type), PingClient α -> α -> Prop :=
| client_send_ocallee (i : Id) (ωs : Ωs) (equ : ωs = snd ω ): o_callee_ping_client ω (SendEC i Ping) tt
| client_recv_ocallee (i : Id) : o_callee_ping_client ω (ReceiveEC i) Pong.

Hint Constructors o_callee_ping_client : ping_p.

Definition client_contract : contract (PingClient) (Ω) := {| 
    witness_update := ping_witness_update ;
    caller_obligation := o_caller_ping_client ;
    callee_obligation := o_callee_ping_client
    (* caller_obligation := fun s A e a => _ ; *)
|}.

(* ============================================================ *)

Definition server_witness_update (ω : Ω) (α : UU0) (e : PingServer α) (a : α) : Ω := 
match e with 
| SendES i m => (fst ω, Some Pong)
| ReceiveES => (fst ω, Some Ping)
end. 

Inductive o_caller_ping_server (ω : Ω) : forall (α : Type), PingServer α -> Prop :=
(* Given the id [i] of a system [ω], a ping message should have been received for a *)
| server_send_ocaller (i : Id) (*equ : ~ is_some x*) : o_caller_ping_server ω (SendES i Pong)
| server_recv_ocaller (*equ : is_some ω*) : o_caller_ping_server ω (ReceiveES).

Hint Constructors o_caller_ping_server : ping_p.


Inductive o_callee_ping_server (ω : Ω) : forall (α : Type), PingServer α -> α -> Prop :=
| server_send_ocallee (i : Id) (*equ : is_some x*): o_callee_ping_server ω (SendES i Pong) tt
| server_recv_ocallee (i : Id) : o_callee_ping_server ω (ReceiveES) i.

Hint Constructors o_callee_ping_server : ping_p.

Definition server_contract : contract (PingServer) (Ω) := make_contract server_witness_update  o_caller_ping_server o_callee_ping_server.

(* ============================================================ *)

Generalizable All Variables.

Section pingMod.        
    (* Context . *)
    (* Context `{Provide jx PingServer}. *)

        (* Variable fclient : impureMonad ix. *)
        (* Variable fserver : impureMonad jx. *)

Definition snd_ping_to `{Provide ix PingClient} { im : impureMonad ix} (s_id:Id):= trigger (im:=im) (inj_p $ SendEC s_id Ping).
Definition rcv_pong_from `{Provide ix PingClient} { im : impureMonad ix} (s_id:Id) := trigger (im:=im) (inj_p $ ReceiveEC s_id).

Definition snd_pong_to `{Provide ix PingServer} { im : impureMonad ix} (s_id:Id):= trigger (im:=im) (inj_p $ SendES s_id Pong).
Definition rcv_ping `{Provide ix PingServer} { im : impureMonad ix} := trigger (im:=im) (inj_p $ ReceiveES).
(* Definition snd_pong_to (c_id:Id) := trigger (im:=fserver) (inj_p $ SendES c_id Pong). *)
(* Definition rcv_ping := trigger (im:=fserver) (inj_p $ ReceiveES). *)

(* ------------ *)

(* Let serv_id := 0%nat.
Let client_id := 1%nat. *)

(* +++ Implem +++ *)

Definition ping_program `{Provide ix PingClient} { im : impureMonad ix} (s_id : Id): im unit := snd_ping_to s_id >> rcv_pong_from s_id >> skip.
Definition pong_program `{Provide ix PingServer} { im : impureMonad ix} : im unit := rcv_ping >>= snd_pong_to >> skip.
(* End pingMod. *)


(* ============================================================ *)

(** ** Intermediary Lemmas *)

(** Closing a door [d] in any system [ω] is always a respectful operation. *)
(*---
Section ping_cli.


Lemma client_respectful `{Provide ix PingClient} {im : impureMonad ix} (ω : Ω) (id : Id)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (client_contract) (ping_program id)) (ω).
Proof.
    prove impure; 
        constructor.
    move: o_caller o_caller0.
        case : ω => /= ωc ωs o_caller o_caller0 eq_ping.
    inversion o_caller0; ssubst => /=.
    inversion o_caller0. subst. ssubst.
Qed.

Hint Resolve client_respectful : ping_p.


Lemma client_run `{Provide ix PingClient} {im : impureMonad ix} (ω : Ω) (u : unit) (ω' : Ω)  (id : Id)
    (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (client_contract) (ping_program id)) ω u ω') :
    ~ is_some ω'.
Proof.

  run_simpl run;
  cleanvert H1.
  cleanvert run.
  cleanvert H1.
  run_simpl H2.
  cleanvert H1.
  cleanvert H2.
  move: equ;
   case: ω => //=.
Qed.

Hint Resolve client_run : ping_p.



Lemma client_respectful_run_inv `{Provide ix PingClient} {im : impureMonad ix} (p : impure ix unit) (ω : Ω) (u : unit) (ω' : Ω)  (id : Id)
(* `{Provide ix DOORS} {A} (p : impure ix A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω)  *)
    (safe : ~ is_some ω)
    (hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) client_contract p) ω)
    (hpost: post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) client_contract p) ω u ω')
  : ~ is_some ω'.
Proof.
    move: ω hpre hpost safe.
    elim: p => [u' | β e k IH] ω hpre run safe.
    + by unroll_post run.
    run_simpl run.
    have hpost :  post (interface_to_hoare client_contract (A:=β) e) ω x ω0
        by split; [apply H1 | by rewrite H2].
    apply/(IH x ω0) => //; [by apply hpre|].
    
    cbn in *;
    inversion hpre; rewrite /= in H4; rewrite /gen_caller_obligation in H4.
    unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *. 
    cbn in *.
    move: hpost H4 H2;
    case: (proj_p e) => [ e' | ] hpost H4 H2.
    - case: hpost => o_callee equω.
        destruct e' as [i m | i].
        + by rewrite equω //=; inversion o_callee; ssubst.
        by subst.
    rewrite H2;
        exact: safe. 
Qed.
End ping_cli.

---*)

(* ============================================================ *)


Section ping_srv.

Lemma server_respectful `{Provide ix PingServer} {im : impureMonad ix} (ω : Ω) (*id : Id*)
  : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (server_contract) (pong_program)) (ω).
Proof.
    prove impure with ping_p ; 
        constructor => //.
Qed.
    (* case: (Some Ping). *)
    (* case: ω; last first. *)
    (* - case: (Some Ping) => //=. admit. *)
    (* case => //=. *)

Hint Resolve server_respectful : ping_p.


Lemma server_run `{Provide ix PingServer} {im : impureMonad ix} (ω : Ω) (u : unit) (ω' : Ω)  (*id : Id*)
    (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (server_contract) (pong_program)) ω u ω') :
    is_some (snd ω').
Proof.

  run_simpl run;
  cleanvert H1.
  cleanvert run.
  cleanvert H1.
  run_simpl H2.
  cleanvert H1.
  cleanvert H2.
  by [].
Qed.

Hint Resolve server_run : ping_p.



Lemma server_respectful_run_inv `{Provide ix PingServer} {im : impureMonad ix} (p : impure ix unit) (ω : Ω) (u : unit) (ω' : Ω)  (id : Id)
(* `{Provide ix DOORS} {A} (p : impure ix A)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (a : A) (ω' : Ω)  *)
    (safe : is_some (snd ω))
    (hpre : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) server_contract p) ω)
    (hpost: post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) server_contract p) ω u ω')
  : is_some (snd ω').
Proof.
    move: ω hpre hpost safe.
    elim: p => [u' | β e k IH] ω hpre run safe.
    + by unroll_post run.
    run_simpl run.
    have hpost :  post (interface_to_hoare server_contract (A:=β) e) ω x ω0
        by split; [apply H1 | by rewrite H2].
    apply/(IH x ω0) => //; [by apply hpre|].
    
    cbn in *;
    inversion hpre; rewrite /= in H4; rewrite /gen_caller_obligation in H4.
    unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *. 
    cbn in *.
    move: hpost H4 H2;
    case: (proj_p e) => [ e' | ] hpost H4 H2.
    - case: hpost => o_callee equω.
        destruct e' as [| a b]; last first.
        + by rewrite equω //=; inversion o_callee; ssubst.
        by subst.
    rewrite H2;
        exact: safe. 
Qed.
End ping_srv.

End pingMod.

(*---

Module probPingMod.
    Section probS.
        Check @prob_interface.
        Context {R : realType}.
        Context `{Provide ix PingClient, Provide ix (prob_interface (R:=R))}.
        Context `{Provide jx PingServer, Provide jx (prob_interface (R:=R))}.

        Variable fclient : impureMonad ix.
        Variable fserver : impureMonad jx.

Check snd_ping_to.



Definition p_snd_ping_to (p : {prob R}) (s_id:Id):= fail_track_op (im:=fclient) p 
    $ (snd_ping_to fclient s_id).
Definition p_rcv_pong_from (p : {prob R}) (s_id:Id):= fail_track_op (im:=fclient) p 
    $ (rcv_pong_from fclient s_id).
Definition p_snd_pong_to (p : {prob R}) (s_id:Id):= fail_track_op (im:=fserver) p 
    $ (snd_pong_to fserver s_id).
Definition p_rcv_ping (p : {prob R}) := fail_track_op (im:=fserver) p 
    $ (rcv_ping fserver).

    (* ------------ *)

Let serv_id := 0%nat.
Let client_id := 1%nat.

Context (p q : {prob R}).
    (* +++ Implem +++ *)

Definition ping_program : fclient (Ω) := p_snd_ping_to p serv_id >> p_rcv_pong_from q serv_id.
Definition pong_program : fserver unit := p_rcv_ping q >>= (fun ox => match ox with | Some x => p_snd_pong_to p x >> skip | None => skip end).

Definition ping_retry_program : fclient (Ω) := p_snd_ping_to p serv_id >>= (fun ox => match ox with None => p_snd_ping_to p serv_id >> skip | _ => skip end) >> p_rcv_pong_from q serv_id.


(* Opaque fail_track_op. *)
(* Arguments fail_track_op : simpl never. *)
(* Goal ping_program = ping_retry_program. *)
(* rewrite/ping_program/ping_retry_program /p_snd_ping_to /p_rcv_pong_from bindA. *)


(* Inductive ProbPingClient : prob_interface :=
| SendEC : Id -> Msg -> PingClient unit
| ReceiveEC : Id -> PingClient Msg.
Inductive PingServer : interface :=
| ReceiveES : PingServer Id
| SendES : Id -> Msg -> PingServer unit. *)
---*)