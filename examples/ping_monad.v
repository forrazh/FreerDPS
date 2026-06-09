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

Inductive Msg := ping|pong.
Definition msg_eq_dec (m m' : Msg) : { m = m' } + { ~ m = m' } :=
  ltac:(decide equality).
(* Channel contains the current message (optional) and whether it has been dropped or not *)

Module ChannelHelper.
    Section sc.
        (* Context {M: failMonad}. *)
Inductive CHANNEL_STATE := Msg.

Definition init_channel : CHANNEL := None.
Definition drop_msg : CHANNEL := fail.
Definition update_msg (m : Msg) (curr : CHANNEL)  : CHANNEL := match curr with
| (_, true) => drop_msg
| _ => (Some m, false)
end.

Definition is_channel_empty (c : CHANNEL) : Prop := match (c.1) with 
| Some _ => False
| _ => True
end.

Definition channel_contains (c : CHANNEL) (m : Msg) := match c with 
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

Fact update_msg_yields_legal_state : forall (c : CHANNEL) (m : Msg), is_legal_state $ update_msg m c.
    by case; case => [m'|]; case.
Qed.

Hint Resolve init_channel_is_legal drop_yields_legal_state update_msg_yields_legal_state : ping_db.


End ChannelHelper.

Import ChannelHelper.
(* ------------------------------------------------------------------------------------ *)

Module CLIENT_M.
    Section client_s.

Print interface.
Inductive IC : interface :=
| SEND : Msg -> IC unit
| WAIT : IC Msg.

Definition send `{Provide ix IC} {im : impureMonad ix} (m : Msg) := trigger (im:=im) (inj_p $ SEND m).
Definition wait `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ WAIT).

Definition C `{Provide ix IC} {im : impureMonad ix} := 
    send (im:=im) ping >> wait.

Check make_contract.

(* 
make_contract
     : forall (i : interface) (Ω : UU0),
(Ω -> forall α : UU0, i α -> α -> Ω) ->
(Ω -> forall α : UU0, i α -> Prop) ->
(Ω -> forall α : UU0, i α -> α -> Prop) ->
contract i Ω
*)
Definition c_step (c : CHANNEL) : forall X : UU0, IC X -> X -> CHANNEL := 
fun X e x =>
match e with
| SEND m => update_msg m c
(* Blocking ?? Where ?? *)
| WAIT => c
end.
(* move => ? e ?; inversion e;subst;
    apply/update_msg/c; [apply/ping | apply/pong].
Defined. *)

Inductive c_o_caller (curr : CHANNEL) : forall X : UU0, IC X -> Prop := 
| SEND_O (eq : is_channel_empty curr) (m : Msg) (eq_cond : m = ping) : c_o_caller curr (SEND m)
| WAIT_O (eq : curr <> drop_msg) (m : Msg) (eq_cond : m = pong) : c_o_caller curr (WAIT).
Hint Constructors c_o_caller : ping_db.

Inductive c_o_callee (curr: CHANNEL) : forall X : UU0, IC X -> X -> Prop :=
| O_SEND (eq : channel_contains curr ping) m : c_o_callee curr (SEND m) tt
| O_WAIT (m : Msg) (eq_cond : m = pong) : c_o_callee curr (WAIT) m.
Hint Constructors c_o_callee : ping_db.

Definition c_contract := make_contract c_step c_o_caller c_o_callee.


Lemma client_respectful `{Provide ix IC} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C)) (init_channel).
Proof.
        (* rework to put only 'prove impure' ? *)
    prove impure with ping_db . constructor => //.
    inversion o_caller0; ssubst.
    inversion eq.
Qed.

Lemma client_run `{Provide ix IC} {im : impureMonad ix} (m : Msg) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C)) (init_channel) m c) 
    : is_legal_state c.
Proof.
        (* rework to put only 'unroll_post' *)
    by run_simpl run;
        cleanvert H1.
Qed.   
    End client_s.
End CLIENT_M.

(* ------------------------------------------------------------------------------------ *)

Module SERVER_M.
    Section server_s.
Inductive IS : interface :=
| RECV : IS Msg
| SNED : Msg -> IS unit.

Definition sned `{Provide ix IS} {im : impureMonad ix} (m : Msg) := trigger (im:=im) (inj_p $ SNED m).
Definition recv `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ RECV).

(**
 * Here we model a recursive server (using fuel as functions must terminate).
 * For convenience purposes, a message is passed to all rounds.
 *)
Fixpoint S_ `{Provide ix IS} {im : impureMonad ix} (fuel : nat) (m : Msg) : im unit := (*fun (X : im T) => *) 
    recv (im:=im) >> 
    sned m >> 
    match fuel with
        | S ful => S_ ful m
        | 0%nat => skip
    end.

Definition s_step (c : CHANNEL) : forall X : UU0, IS X -> X -> CHANNEL :=
fun X e x => 
match e with 
| RECV => c
| SNED m => update_msg m c
end.
(* move => ? e ?; inversion e;subst; *)
    (* apply/update_msg/c; [apply/ping | apply/pong]. *)
(* Defined. *)

(* Inductive s_o_caller (curr : CHANNEL) : forall X : UU0, IS X -> Prop :=  *)
(* | RECV_O (m : Msg) : s_o_caller curr (RECV) *)
(* | SNED_O : s_o_caller curr SNED. *)
(* Hint Constructors s_o_caller : ping_db. *)

Inductive s_o_callee (curr: CHANNEL) : forall X : UU0, IS X -> X -> Prop :=
| O_RECV (eq : channel_contains curr ping) (m : Msg) : s_o_callee curr (RECV) m
| O_SNED (eq : channel_contains curr pong) (m : Msg) : s_o_callee curr (SNED pong) tt.
Hint Constructors s_o_callee : ping_db.

Definition s_contract := make_contract s_step no_caller_obligation s_o_callee.

Let ping_sent := (Some ping, false).

Lemma server_respectful `{Provide ix IS} {im : impureMonad ix} (fuel : nat)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract) (S_ fuel ping)) (ping_sent).
Proof.
    elim : fuel => [|ful EH]; prove impure with ping_db.
Qed.

Lemma server_run `{Provide ix IS} {im : impureMonad ix} (m : Msg) (c : CHANNEL) (fuel : nat)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract) (S_ fuel ping)) (ping_sent) tt c) 
    : is_legal_state c.
Proof.
    by move : run; 
        elim : fuel => [|ful EH] run; 
            [| apply/EH];
        (* rework to put only 'unroll_post' *)
        run_simpl run; 
            cleanvert H1; cleanvert run; cleanvert H1; 
            run_simpl H2; cleanvert H1.
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

Definition prog `{Provide ix IC, Provide ix IS} {im: impureMonad ix} := 
    send (im:=im) ping >> 
    recv >>
    sned pong >>  
    wait. 

Definition cs_contract := sharedcontractprod CLIENT_M.c_contract SERVER_M.s_contract.

Lemma v1_respectful `{Provide ix IC, Provide ix IS} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel).
Proof.
        prove impure with ping_db.
Qed.

Lemma v1_run `{Provide ix IC, Provide ix IS} {im : impureMonad ix} (m : Msg) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel) m c)
    : is_legal_state c.
Proof.
    (* Make everything go through 'unroll_post' *)
    by run_simpl run; 
        cleanvert run; cleanvert H3; cleanvert H4; cleanvert H3;
        cleanvert  H5; cleanvert H3; cleanvert H5; cleanvert H3; 
        cleanvert  H5; cleanvert H6; cleanvert H4; cleanvert H3; 
        cleanvert  H4; cleanvert H3; cleanvert H5.
Qed.

End V1_M.

(* ------------------------------------------------------------------------------------ *)
(* Inductive IN : interface :=
| DLVR (m : Msg) : IN Msg
| DROP (m : Msg) : IN Msg.

Definition deliver `{Provide ix IN} {im : impureMonad ix} (m : Msg) := trigger (im:=im) (inj_p $ DLVR m).
Definition drop `{Provide ix IN} {im : impureMonad ix} (m : Msg) := trigger (im:=im) (inj_p $ DROP m). *)

Module NETWORK_M.
    Section network_s.

(**
    A message may be dropped or delivered. This sounds like an option, could be :
    ```
Definition packet_transfer := option Msg.
    ```

    Maybe a simple bool is better.
 *)


Definition packet_transfer := option Msg.

Inductive IN : interface :=
| DELIVER : Msg -> IN bool.
(* Message may be dropped *)

(* Channel devrait ptet être une monade *)
Definition n_step (c : CHANNEL) : forall X : UU0, IN X -> X -> CHANNEL.
    move => X e produ.
        inversion e; subst.
        case eq : produ;
            [ apply: update_msg H c | apply/drop_msg ].
Defined.

(* Inductive n_o_caller (curr : CHANNEL) : forall X : UU0, IN X -> Prop := 
| DELIVER_O (m : Msg) : n_o_caller curr (DELIVER m).
Hint Constructors n_o_caller : ping_db. *)

Definition legal_delivery (p : bool) (c : CHANNEL) : Prop := c.2 <> p.

Inductive n_o_callee (curr: CHANNEL) : forall X : UU0, IN X -> X -> Prop :=
| O_DELIVER (m : Msg) (p : packet_transfer) (eq : legal_delivery p curr) : n_o_callee curr (DELIVER m) p.
Hint Constructors n_o_callee : ping_db. 

Definition deliver `{Provide ix IN} {im : impureMonad ix} (m : Msg) := trigger (im:=im) (inj_p $ DELIVER m).

(* Definition n_contract := make_contract n_step n_o_caller n_o_callee. *)
Definition n_contract := make_contract n_step no_caller_obligation n_o_callee.

Lemma network_respectful `{Provide ix IN} {im : impureMonad ix} (c : CHANNEL) (m : Msg)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (n_contract) (deliver m)) (c).
Proof. 
    prove impure with ping_db.
Qed.

Lemma network_run `{Provide ix IN} {im : impureMonad ix} (packet : packet_transfer) msg (initial_state_channel  final_state_channel: CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (n_contract) (deliver msg)) initial_state_channel packet final_state_channel) 
    : is_legal_state initial_state_channel -> is_legal_state final_state_channel.
Proof.
    move => Hlegal.
    (* Make everything go through 'unroll_post' *)
    run_simpl run; 
        cleanvert H1; cleanvert H2; 
        cleanvert H1; cleanvert H3.
    move : H2.
    case : packet => /= [m |];
        rewrite /gen_witness_update/gen_callee_obligation; 
        case (proj_p (inj_p $ DELIVER msg)) => //= i H'.
    all: inversion H'; ssubst => //=.
    move : eq. rewrite /legal_delivery/is_legal_state/update_msg/drop_msg.

    by case initial_state_channel => //=; case => [m'|]; case.
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

        Definition prog `{Provide ix IC, Provide ix IN} {im: impureMonad ix} : im unit:= 
        send (im:=im) ping >> deliver ping >>= fun p => match p with
        | true => wait >> skip
        | false => skip
        end.

Definition cn_contract := sharedcontractprod c_contract n_contract.

Lemma cn_respectful `{Provide ix IC, Provide ix IN} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cn_contract) (prog)) (init_channel).
Proof.
        by prove impure with ping_db; case x0.
Qed.

Lemma cn_run `{Provide ix IC, Provide ix IN} {im : impureMonad ix} (m : Msg) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cn_contract) (prog)) (init_channel) tt c)
    : is_legal_state c.
Proof.
    run_simpl run; cleanvert run; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H4.
    move : H5; case x0 => /= H5.
    - by cleanvert H5; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H4.

    by cleanvert H5.
Qed.

    End client_faulty_s.
End CLIENT_FAULTY_NETWORK_M.


(* ------------------------------------------------------------------------------------ *)

(**
    Now, lets try to model the server interacting with the network.

(a)    +---+ ==> (1)  dlvr ping  ==> +---+ 
       | N |                         | S | 
(b)    +---+ <== (2) answer pong <== +---+ 

**)
(* ------------------------------------------------------------------------------------ *)

Module SERVER_FAULTY_NETWORK_M.
    Section server_faulty_s.

        (* Definition faulty_sned `{Provide ix IS, Provide ix IN} {im: impureMonad ix} : im packet_transfer := < sned >.  *)

Fixpoint prog `{Provide ix IS, Provide ix IN} {im : impureMonad ix} (fuel : nat) (msg : Msg) : im unit := (*fun (X : im T) => *) 
    (* add message deliverance *)
    deliver msg >>= fun p => match p with
    | true => recv >> 
                sned pong >> 
    (* add message deliverance... needed ? *)
                match fuel with
                    | S ful => prog ful msg
                    | 0%nat => skip
                end
    | false => match fuel with
                | S ful => prog ful msg
                | 0%nat => skip
            end
    end.

(* 
        Program Definition prog `{Provide ix IS, Provide ix IN} {im: impureMonad ix} : im packet_transfer := 
            deliver >>= fun p => _.
        Next Obligation.
            move => ix Hmp_s Hp_s Hmp_n Hp_n im; case => [m|].
            - apply/bind => [| m']. apply/recv. apply/bind => [| m'']. apply/sned. apply/deliver.
            apply/Ret/None.
        Show Proof.
        Defined.  *)

Let ping_sent := (Some ping, false).
Print init_channel.

Definition sn_contract := sharedcontractprod s_contract n_contract.

Lemma sn_respectful `{Provide ix IS, Provide ix IN} {im : impureMonad ix} (fuel : nat)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (sn_contract) (prog fuel ping)) (ping_sent).
Proof.
    elim: fuel => [|ful EH];
     prove impure with ping_db;
        (** 
          * probably lacks a // in tactic... but probably not tbf... 
          * The question might be 'do we want to make the tactic automatically destruct things ?'  *)
            case : x => // m.
    
    (* prove impure with ping_db. *)
Qed.

Lemma sn_run `{Provide ix IS, Provide ix IN} {im : impureMonad ix} (fuel : nat) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (sn_contract) (prog fuel ping)) (ping_sent) tt c)
    : is_legal_state c.
Proof.
    move: run;
    elim: fuel => [|ful EH] run; [|apply/EH].
    - by run_simpl run; move: run; case x => run; cleanvert run; run_simpl H3; cleanvert H3 => //;
        cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H6.

    by run_simpl run ; move: run; case x => run; [| | rewrite -H4 | rewrite -H4] => //;
        cleanvert run; run_simpl H3; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H3.
Qed.

    End server_faulty_s.
End SERVER_FAULTY_NETWORK_M.


(**
    Now, lets try to model this :

(a)    +---+ ==> (1) send ping ==> +---+ ==> (2) dlvr ping ==> +---+ 
       | C |                       | N |                       | S |
(b)    +---+ <== (4) dlvr pong <== +---+ <== (4) send pong <== +---+

**)
Module V2_M.
    Section v2_s.


Definition prog `{Provide ix IC, Provide ix IS, Provide ix IN} {im: impureMonad ix} := 
    (* C *) send (im:=im) ping >>
    (* N *) deliver ping >>= fun p => match p with 
        | true =>
    (* S *) recv >> 
    (* S *) sned pong >>
    (* N *) deliver pong >>= fun p => match p with 
        | true => 
    (* C *) wait >> skip
        | false => skip
        end    
        | false => skip
        end.

Local Open Scope contract_scope.

Definition cns_contract := c_contract ^ n_contract ^ s_contract.

Lemma cns_respectful `{Provide ix IC, Provide ix IS, Provide ix IN} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cns_contract) (prog)) (init_channel).
Proof.
    prove impure with ping_db;
        case : x0 => // m.
    (* by prove impure with ping_db;
        case : x2. *)
Qed.

Lemma cns_run `{Provide ix IC, Provide ix IS, Provide ix IN} (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cns_contract) (prog)) (init_channel) tt c)
    : is_legal_state c.
Proof.
    run_simpl run; cleanvert run; cleanvert H5; cleanvert H6; cleanvert H5; cleanvert H6.
    move: H7; case : x0 => /= run; cleanvert run; cleanvert H5 => //.
    
    by cleanvert H6; cleanvert H7; cleanvert H5; cleanvert H6; cleanvert H5; cleanvert H8; cleanvert H5; cleanvert H8; cleanvert H6; cleanvert H8; cleanvert H5; cleanvert H6; cleanvert H7 => //;
        move: H9; case : x3 => //= run; cleanvert run; cleanvert H5 => //; cleanvert H6; cleanvert H5; cleanvert H7.
Qed.

    End v2_s.
End V2_M.

(* Definition simple_one_round_fail_prog `{Provide ix IC, Provide ix IS, Provide ix N} {im : impureMonad ix} : im unit :=

(* (a) *)    send (im:=im) >>= fun m => deliver m >>= fun om => match om with | Some _ => recv >> 
(* (b) *)    sned          >>= fun m => deliver m >>= fun om => match om with | Some _ => wait >> skip
    | _ => skip end 
| _ => skip    
    end. *)
