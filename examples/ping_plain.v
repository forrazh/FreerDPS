From monae Require Import preamble hierarchy.

(* From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct. *)
(* From infotheo Require Import realType_ext ssr_ext fsdist convex. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq path.
From FreerDPS Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Obligation Tactic := simpl.

Generalizable All Variables. 
Local Open Scope monae_scope.

Create HintDb ping_db.

Inductive M := ping|pong.

(* Channel contains the current message (optional) and whether it has been dropped or not *)
Definition CHANNEL := (option M * bool).

Module ChannelHelper.
Definition init_channel : CHANNEL := (None, false).
Definition drop_msg : CHANNEL := (None, true).
Definition update_msg (m : M) (curr : CHANNEL)  : CHANNEL := match curr with
| (_, true) => drop_msg
| _ => (Some m, false)
end.

Definition is_channel_empty (c : CHANNEL) : Prop := match (c.1) with 
| Some _ => False
| _ => True
end.

Definition channel_contains (c : CHANNEL) (m : M) := match c with 
| (_, true) => False
| (Some m', false) => match m, m' with 
    | ping, ping => True
    | pong, pong => True
    | _, _ => False
    end
| _ => False
end.

Definition is_legal_state (c : CHANNEL) : Prop := match c with
| (Some _, true) => False
(* | (Some _, false) => True *)
(* | (None, false) *)
| (_, _) => True
end.

Fact init_channel_is_legal : is_legal_state init_channel.
Proof.
    done.
Qed.

Fact drop_yields_legal_state : is_legal_state drop_msg.
    done.
Qed.

Fact update_msg_yields_legal_state : forall (c : CHANNEL) (m : M), is_legal_state $ update_msg m c.
    by case; case => [m'|]; case.
Qed.

Hint Resolve init_channel_is_legal drop_yields_legal_state update_msg_yields_legal_state : ping_db.


End ChannelHelper.

Import ChannelHelper.
(* ------------------------------------------------------------------------------------ *)

Module CLIENT_M.
    Section client_s.

Inductive IC : interface :=
| SEND : IC M
| WAIT : M -> IC unit.

Definition send `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SEND).
Definition wait `{Provide ix IC} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ WAIT m).

Definition C `{Provide ix IC} {im : impureMonad ix} := send (im:=im) >> (wait pong).

Check make_contract.

(* 
make_contract
     : forall (i : interface) (Ω : UU0),
(Ω -> forall α : UU0, i α -> α -> Ω) ->
(Ω -> forall α : UU0, i α -> Prop) ->
(Ω -> forall α : UU0, i α -> α -> Prop) ->
contract i Ω
*)
Definition c_step (c : CHANNEL) : forall X : UU0, IC X -> X -> CHANNEL.
move => ? e ?; inversion e;subst;
    apply/update_msg/c; [apply/ping | apply/pong].
Defined.

Inductive c_o_caller (curr : CHANNEL) : forall X : UU0, IC X -> Prop := 
| SEND_O (eq : is_channel_empty curr) : c_o_caller curr SEND
| WAIT_O (eq : curr <> drop_msg) (m : M) (eq_cond : m = pong) : c_o_caller curr (WAIT m).
Hint Constructors c_o_caller : ping_db.

Inductive c_o_callee (curr: CHANNEL) : forall X : UU0, IC X -> X -> Prop :=
| O_SEND (eq : channel_contains curr ping) : c_o_callee curr SEND ping
| O_WAIT (m : M) (eq_cond : m = pong) : c_o_callee curr (WAIT m) tt.
Hint Constructors c_o_callee : ping_db.

Definition c_contract := make_contract c_step c_o_caller c_o_callee.


Lemma client_respectful `{Provide ix IC} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C)) (init_channel).
Proof.
    prove impure with ping_db; constructor => //.
Qed.

Lemma client_run `{Provide ix IC} {im : impureMonad ix} (m : M) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C)) (init_channel) tt c) 
    : is_legal_state c.
Proof.
    (* rewrite /is_legal_state. *)
    by run_simpl run;
        cleanvert H1;
        cleanvert run;
        cleanvert H1;
        cleanvert H2;
        cleanvert H3.
Qed.   
    End client_s.
End CLIENT_M.

(* ------------------------------------------------------------------------------------ *)

Module SERVER_M.
    Section server_s.
Inductive IS : interface :=
| RECV : IS M
| SNED : IS M.

Definition sned `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SNED).
Definition recv `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ RECV).

(**
 * Here we model a recursive server (using fuel as functions must terminate).
 *)
Fixpoint S_ `{Provide ix IS} {im : impureMonad ix} (fuel : nat) : im unit := (*fun (X : im T) => *) recv (im:=im) >> sned >> match fuel with
| S ful => S_ ful
| 0%nat => skip
end.

Definition s_step (c : CHANNEL) : forall X : UU0, IS X -> X -> CHANNEL.
move => ? e ?; inversion e;subst;
    apply/update_msg/c; [apply/ping | apply/pong].
Defined.

Inductive s_o_caller (curr : CHANNEL) : forall X : UU0, IS X -> Prop := 
| RECV_O : s_o_caller curr RECV
| SNED_O : s_o_caller curr SNED.
Hint Constructors s_o_caller : ping_db.

Inductive s_o_callee (curr: CHANNEL) : forall X : UU0, IS X -> X -> Prop :=
| O_RECV (eq : channel_contains curr ping) : s_o_callee curr RECV ping
| O_SNED (eq : channel_contains curr pong) : s_o_callee curr SNED pong.
Hint Constructors s_o_callee : ping_db.

Definition s_contract := make_contract s_step s_o_caller s_o_callee.

Let ping_sent := (Some ping, false).

Lemma server_respectful `{Provide ix IS} {im : impureMonad ix} (fuel : nat)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract) (S_ fuel)) (ping_sent).
Proof.
    elim : fuel => [|ful EH].
    - by prove impure with ping_db ; constructor.
    
    prove impure with ping_db.
    cleanvert o_caller2;
        inversion eq.


Qed.

Lemma server_run `{Provide ix IS} {im : impureMonad ix} (m : M) (c : CHANNEL) (fuel : nat)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract) (S_ fuel)) (ping_sent) tt c) 
    : is_legal_state c.
Proof.
    move : run ; elim : fuel => [|ful EH] run.
    {
        run_simpl run; cleanvert H1; cleanvert run; cleanvert H1.
        by run_simpl H2; cleanvert H1.
    }
    apply/EH.
    (* rewrite /is_legal_state. *)
    run_simpl run; 
    cleanvert H1;
    cleanvert run;
    cleanvert H1;
    cleanvert H2;
    cleanvert H1.

    move : H3 H2 eq => /=.
    rewrite /gen_callee_obligation /gen_witness_update.
    case (proj_p (inj_p SNED)) => [e |];
    case : x => //= H3 H2 eq.

    all: by cleanvert H2; [apply/H3 | inversion eq0].
Qed.   

End server_s.
End SERVER_M.

(* ------------------------------------------------------------------------------------ *)

(**
    Let's first try to model this :

(a)    +---+ ==> (1) send ping   ==> +---+ 
       | C |                         | S |
(b)    +---+ <== (2) answer pong <== +---+

**)

Import CLIENT_M SERVER_M.

Module V1_M.

Definition prog `{Provide ix IC, Provide ix IS} {im: impureMonad ix} := send (im:=im) >> recv >> sned >>= fun m => wait m. 

Definition cs_contract := sharedcontractprod CLIENT_M.c_contract SERVER_M.s_contract.

Lemma v1_respectful `{Provide ix IC, Provide ix IS} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel).
Proof.
        prove impure with ping_db; constructor => //.
Qed.

Lemma v1_run `{Provide ix IC, Provide ix IS} {im : impureMonad ix} (m : M) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel) tt c)
    : is_legal_state c.
Proof.
    run_simpl run; cleanvert run; cleanvert H3; cleanvert H4; cleanvert H3.
    cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H6.
    cleanvert H4; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H4.
    done.
Qed.

(* ------------------------------------------------------------------------------------ *)
(* Inductive IN : interface :=
| DLVR (m : M) : IN M
| DROP (m : M) : IN M.

Definition deliver `{Provide ix IN} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DLVR m).
Definition drop `{Provide ix IN} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DROP m). *)

Module NETWORK_M.
    Section network_s.

(**
    A message may be dropped or delivered. This sounds like an option, could be :
    ```
Definition packet_transfer := option M.
    ```

    Maybe a simple bool is better.
 *)


Inductive packet_transfer :=
| DELIVERED : M -> packet_transfer
| DROPPED : packet_transfer. 

Inductive IN : interface :=
| DELIVER : IN packet_transfer.
(* Message may be dropped *)

Definition n_step (c : CHANNEL) : forall X : UU0, IN X -> X -> CHANNEL.
    move => X e packet;
        inversion e; subst;
        case : packet => [m |]; 
            [ apply: update_msg m c | apply/drop_msg ].
Defined.

Inductive n_o_caller (curr : CHANNEL) : forall X : UU0, IN X -> Prop := 
| DELIVER_O : n_o_caller curr DELIVER.
Hint Constructors n_o_caller : ping_db.

Inductive n_o_callee (curr: CHANNEL) : forall X : UU0, IN X -> X -> Prop :=
| O_DELIVER (p : packet_transfer) : n_o_callee curr DELIVER p.
Hint Constructors n_o_callee : ping_db.

Definition deliver `{Provide ix IN} {im : impureMonad ix} := trigger (im:=im) (inj_p $ DELIVER).

Definition n_contract := make_contract n_step n_o_caller n_o_callee.

Lemma network_respectful `{Provide ix IN} {im : impureMonad ix} (c : CHANNEL)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (n_contract) (deliver)) (c).
Proof. 
    prove impure with ping_db.
Qed.

Lemma network_run `{Provide ix IN} {im : impureMonad ix} (packet : packet_transfer) (initial_state_channel  final_state_channel: CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (n_contract) (deliver)) initial_state_channel packet final_state_channel) 
    : is_legal_state initial_state_channel -> is_legal_state final_state_channel.
Proof.
    move => Hlegal.
    run_simpl run; cleanvert H1; cleanvert H2; cleanvert H1; cleanvert H3.
    move : H2.
    case : packet => /= [m |];
        rewrite /gen_witness_update/gen_callee_obligation; 
        case (proj_p (inj_p DELIVER)) => //= i H'; cleanvert H' => //=.
    
    exact: update_msg_yields_legal_state. 
Qed.

    End network_s.
End NETWORK_M.

Import NETWORK_M.

(* ------------------------------------------------------------------------------------ *)

(**
    Now, lets try to model the client interacting with the network.

(a)    +---+ ==> (1) send ping ==> +---+ 
       | C |                       | N | 
(b)    +---+ <== (2) dlvr pong <== +---+ 

**)

Module CLIENT_FAULTY_NETWORK_M.
    Section client_faulty_s.

        Program Definition prog `{Provide ix IC, Provide ix IN} {im: impureMonad ix} : im unit:= send (im:=im) >> deliver >>= fun p => _.
        Next Obligation.
            move => ix Hmp_c Hp_c Hmp_n Hp_n im; case => [m|].
            - apply/wait/m.
            apply/skip.
        Defined. 

Definition cn_contract := sharedcontractprod c_contract n_contract.

Lemma cn_respectful `{Provide ix IC, Provide ix IN} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cn_contract) (prog)) (init_channel).
Proof.
        prove impure with ping_db.
        by case : x0.
Qed.

Lemma cn_run `{Provide ix IC, Provide ix IN} {im : impureMonad ix} (m : M) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cn_contract) (prog)) (init_channel) tt c)
    : is_legal_state c.
Proof.
    run_simpl run; cleanvert run; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H4.
    move : H5; case x0 => /= [m' |] H5.
    - by cleanvert H5; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H4.

    by cleanvert H5.
Qed.


(* ------------------------------------------------------------------------------------ *)

(**
    Now, lets try to model the server interacting with the network.

(a)    +---+ ==> (1)  dlvr ping  ==> +---+ 
       | N |                         | S | 
(b)    +---+ <== (2) answer pong <== +---+ 

**)
(* ------------------------------------------------------------------------------------ *)

(**
    Now, lets try to model this :

(a)    +---+ ==> (1) send ping ==> +---+ ==> (2) dlvr ping ==> +---+ 
       | C |                       | N |                       | S |
(b)    +---+ <== (4) dlvr pong <== +---+ <== (4) send pong <== +---+

**)

(* Definition simple_one_round_fail_prog `{Provide ix IC, Provide ix IS, Provide ix N} {im : impureMonad ix} : im unit :=

(* (a) *)    send (im:=im) >>= fun m => deliver m >>= fun om => match om with | Some _ => recv >> 
(* (b) *)    sned          >>= fun m => deliver m >>= fun om => match om with | Some _ => wait >> skip
    | _ => skip end 
| _ => skip    
    end. *)
