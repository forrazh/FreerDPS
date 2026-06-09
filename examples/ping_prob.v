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
Definition msg_eq_dec (m m' : M) : { m = m' } + { ~ m = m' } :=
  ltac:(decide equality).
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

From mathcomp Require Import mathcomp_extra ssrnum ring lra reals Rstruct interval_inference.
From infotheo Require Import realType_ext ssr_ext fsdist.
From monae Require Import proba_model proba_lib.

Module ProbMessageM.
    Section prob_msg_s.
        Local Open Scope proba_scope.
        Local Open Scope ring_scope.
        Local Open Scope reals_ext_scope.
        Local Open Scope convex_scope.

        Context {R : realType} {pm : probMonad R}.

(** 
  * 
  *)
Definition prob_ping_or_pong (p : {prob R}) : pm M.
    apply/choice.
    - apply/p.
    - apply/Ret. apply/ping.
    - apply/Ret/pong.
Defined.

Definition may_deliver (p_failure : {prob R}) (m : M) : pm (option M).
        apply/choice.
        - apply/p_failure.
        - apply/Ret/None.
        apply/Ret/Some/m.
    Defined.
    
    
Definition prog (p : {prob R}) := may_deliver p ping >>= fun m => 
match m with 
| Some _ => may_deliver p pong
| None => Ret None
end.

(* x1: p
   x2: (1 - p) * p
   ----
   x1 + x2
   p + p - pp
   2p - pp
   (2 - p)p
   *)

Definition prog' (p : {prob R}) := may_deliver (probmulr (p%:num.~)%:i01 (p%:num.~)%:i01) pong.

From HB Require Import structures.

Check probmulr.
(* Goal forall p q, s_of_pq p q = probmulr (R:=R) (p%:num.~)%:i01 (q%:num.~)%:i01.
        move=> p q.
        rewrite /s_of_pq /probmulr.
        move => /=.
        Search _.~.

(* 
    Where do I put the probability ??
    Where does non determinism occur if you look at disel ? 
    Same for Aneris or Ado.

    Does FreeSpec show an example of non det ?
    But, if that's the case, where do I put the probability in my interface ??
*)

        (*  s.~ = p.~ * q.~ = p + (p.~ * q)
            1 - ((1 - p) * (1 - q)) = p + ((1 - p) * q)
            1 - (1 - q - (p - pq)) = p + (q - pq)
            1 - (1 - q - p + pq) = p + q - pq
            1 - 1 + q + p - pq = p + q - pq
            0 + q + p - pq = p + q - pq


            s.~ = p.~ * q.~ -> s = (p.~ * q.~).~
            1 - (1 - ((1 - p) * (1 - q))) = p + ((1 - p) * q)
            1 - (1 - ((1 - q) - (p - pq))) = p + (q - pq)
            1 - (1 - (1 - q - p + pq)) = p + q - pq
            1 - (1 - 1 + q + p - pq) = p + q - pq
            1 - q - p + pq = p + q - pq
            1 - (1 - ((1 - p) * (1 - q))) = p + ((1 - p) * q)
            1 - (1 - ((1 - p) * (1 - q))) = p + ((1 - p) * q)

            (1 - p) * (1 - q) = p + ((1 - p) * q)
            (1 - q) - (p - pq) = p + (q - pq) 
            (1 - q) - p + pq = p + q - pq
            (1 - q) - p 
            
            
            
            1 - (1 - q) - (p - pq) = 
            1 + (-1 + q + (-p + pq)) = p + q - pq
            1-1 + q - p + pq = p + q - pq
            pq - p = p - pq
            p (q - 1) = p (1 - q)  
            pq + q = 1 - q + pq
            q = 1 - q
        *)
        Check choiceA. *)

Goal forall p, prog p = prog' p.
    move => p.
    rewrite /prog/prog'/may_deliver!choice_bindDl!bindretf choiceA choicemm /s_of_pq /probmulr /=.
    Admitted.
    




    End prob_msg_s.
End ProbMessageM.
    


(* ------------------------------------------------------------------------------------ *)

Module CLIENT_M.
    Section client_s.

Inductive IC : interface :=
| SEND : IC M
| WAIT : M -> IC unit.

Definition send `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SEND).
Definition wait `{Provide ix IC} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ WAIT m).

Definition C `{Provide ix IC} {im : impureMonad ix} := send (im:=im) >> (wait pong).

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
        (* rework to put only 'prove impure' ? *)
    by prove impure with ping_db; constructor.
Qed.

Lemma client_run `{Provide ix IC} {im : impureMonad ix} (m : M) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C)) (init_channel) tt c) 
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
| RECV : M -> IS unit
| SNED : IS M.

Definition sned `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SNED).
Definition recv `{Provide ix IS} {im : impureMonad ix} (m : M):= trigger (im:=im) (inj_p $ RECV m).

(**
 * Here we model a recursive server (using fuel as functions must terminate).
 * For convenience purposes, a message is passed to all rounds.
 *)
Fixpoint S_ `{Provide ix IS} {im : impureMonad ix} (fuel : nat) (m : M) : im unit := (*fun (X : im T) => *) 
    recv (im:=im) m >> 
    sned >> 
    match fuel with
        | S ful => S_ ful m
        | 0%nat => skip
    end.

Definition s_step (c : CHANNEL) : forall X : UU0, IS X -> X -> CHANNEL.
move => ? e ?; inversion e;subst;
    apply/update_msg/c; [apply/ping | apply/pong].
Defined.

Inductive s_o_caller (curr : CHANNEL) : forall X : UU0, IS X -> Prop := 
| RECV_O (m : M) : s_o_caller curr (RECV m)
| SNED_O : s_o_caller curr SNED.
Hint Constructors s_o_caller : ping_db.

Inductive s_o_callee (curr: CHANNEL) : forall X : UU0, IS X -> X -> Prop :=
| O_RECV (eq : channel_contains curr ping) (m : M) : s_o_callee curr (RECV m) tt
| O_SNED (eq : channel_contains curr pong) : s_o_callee curr SNED pong.
Hint Constructors s_o_callee : ping_db.

Definition s_contract := make_contract s_step s_o_caller s_o_callee.

Let ping_sent := (Some ping, false).

Lemma server_respectful `{Provide ix IS} {im : impureMonad ix} (fuel : nat)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract) (S_ fuel ping)) (ping_sent).
Proof.
    elim : fuel => [|ful EH]; prove impure with ping_db.
    
    by cleanvert o_caller2.
Qed.

Lemma server_run `{Provide ix IS} {im : impureMonad ix} (m : M) (c : CHANNEL) (fuel : nat)
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

Definition prog `{Provide ix IC, Provide ix IS} {im: impureMonad ix} := send (im:=im) >>= recv >> sned >>= fun m => wait m. 

Definition cs_contract := sharedcontractprod CLIENT_M.c_contract SERVER_M.s_contract.

Lemma v1_respectful `{Provide ix IC, Provide ix IS} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel).
Proof.
        prove impure with ping_db.
Qed.

Lemma v1_run `{Provide ix IC, Provide ix IS} {im : impureMonad ix} (m : M) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cs_contract) (prog)) (init_channel) tt c)
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
Definition packet_transfer := option M.

Inductive IN : interface :=
| DELIVER : M -> IN packet_transfer.
(* Message may be dropped with prob p *)

Definition n_step (c : CHANNEL) : forall X : UU0, IN X -> X -> CHANNEL.
    move => X e packet;
        inversion e; subst.
        case : packet => [m |]; 
            [ apply: update_msg m c | apply/drop_msg ].
Defined.

Inductive n_o_caller (curr : CHANNEL) : forall X : UU0, IN X -> Prop := 
| DELIVER_O (m : M) : n_o_caller curr (DELIVER m).
Hint Constructors n_o_caller : ping_db.

Definition legal_delivery (p : packet_transfer) (m : M) : Prop := match p with
| Some m' => m = m'
| None => True
end.

Inductive n_o_callee (curr: CHANNEL) : forall X : UU0, IN X -> X -> Prop :=
| O_DELIVER (m : M) (p : packet_transfer) (eq : legal_delivery p m) : n_o_callee curr (DELIVER m) p.
Hint Constructors n_o_callee : ping_db.

Definition deliver `{Provide ix IN} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DELIVER m).

Definition n_contract := make_contract n_step n_o_caller n_o_callee.

Lemma network_respectful `{Provide ix IN} {im : impureMonad ix} (c : CHANNEL) (m : M)
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
    
    exact: update_msg_yields_legal_state. 
Qed.

    End network_s.
End NETWORK_M.

Import NETWORK_M.


Module FAIL_M.
    Section fail_s.


Context {R : realType} {sample : {prob R}}.

Variable prob_hoare : hoareMonad + probMonad R.

(* Variable p : {prob R}. *)

Definition f (p : {prob R}) : bool.
    Admitted.
(* Variable p : {prob R}. *)
(* Check f p%:num.~%:i01. *)
(* Check p%:num.~%:i01. *)

(* Inductive prob_packet : forall (p: {prob R}), UU0 :=. *)

About prob_packet.

Variable fl : probMonad R.
Inductive FlipEff : UU0 -> UU0 :=
| flip_e (p : {prob R}) : FlipEff bool
.


(* Variable M : (impureMonad FlipEff). *)


Definition flipf `{Provide ix FlipEff} {im : impureMonad ix} (p:{prob R}) : im bool := ( trigger (im:=im) (inj_p $ flip_e p)).

Definition denote_flip_effect : FlipEff ~~> fl :=
fun X fx => match fx with 
| flip_e p => bcoin p
end.

Notation choice_of_Type := monad_model.choice_of_Type.

Check (choice_of_Type (option M)).

Definition choicef `{Provide ix FlipEff} {im : impureMonad ix} {X} (p : {prob R}) (a b : X) : im X := flipf p >>= (fun b0 => if b0 then Ret a else Ret b).

Notation "x <|| p ||> y" := 
  (choicef p x y) 
(at level 40, left associativity, y at next level).

Print bcoin.
(* Definition prob_packet (p : {prob R}) m : option M := choice p (option M) (Ret None) (Ret $ Some m). *)


Record prob_packet (p : {prob R}):= {
    message : packet_transfer;
    (* message_dropped with prob  p ; *)
    }.

(* | DROPPED : prob_packet p *)
(* | DELIVERED (m : M) : prob_packet (sample%:num.~%:i01). *)

(* Check DROPPED. *)
Check prob_packet sample.

Variable pack : prob_packet sample.

Inductive IPN : interface :=
| TRANSMIT (p : prob_packet sample) : IPN M.

About TRANSMIT.
Inductive  IFail : {prob R} -> interface := 
| FAIL : forall p, IFail p unit
| SUCC : forall p, IFail p%:num.~%:i01 M.

Program Definition f_step {p : {prob R}} (c : CHANNEL) : forall X : UU0, IFail p X -> X -> CHANNEL.
    move => X e m;
        inversion e; subst.
        - apply/drop_msg.
        apply: update_msg m c.
Defined.
Print f_step. 

Inductive n_o_caller (curr : CHANNEL) : forall X : UU0, IN X -> Prop := 
| DELIVER_O (m : M) : n_o_caller curr (DELIVER m).
Hint Constructors n_o_caller : ping_db.

Definition legal_delivery (p : packet_transfer) (m : M) : Prop := match p with
| Some m' => m = m'
| None => True
end.

Inductive n_o_callee (curr: CHANNEL) : forall X : UU0, IN X -> X -> Prop :=
| O_DELIVER (m : M) (p : packet_transfer) (eq : legal_delivery p m) : n_o_callee curr (DELIVER m) p.
Hint Constructors n_o_callee : ping_db.


Program Definition may_deliver `{Provide ix (IFail p), Provide ix IN} {im : impureMonad ix} (m : M) : im packet_transfer := _.
 (* may_do p >>= fun b => if b then deliver m else Ret None. *)
Next Obligation.
    move=>ix p Hmp_f Hp_f Hmp_n Hp_n im m.
    apply/trigger. 
    End fail_s.
End FAIL_M.


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
        send (im:=im) >>= deliver >>= fun p => match p with
        | Some m => wait m
        | None => skip
        end.

Definition cn_contract := sharedcontractprod c_contract n_contract.

Lemma cn_respectful `{Provide ix IC, Provide ix IN} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cn_contract) (prog)) (init_channel).
Proof.
        by prove impure with ping_db; case x0.
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

Fixpoint prog `{Provide ix IS, Provide ix IN} {im : impureMonad ix} (fuel : nat) (msg : M) : im unit := (*fun (X : im T) => *) 
    (* add message deliverance *)
    deliver msg >>= fun p => match p with
    | Some m => recv m >> 
                sned >> 
    (* add message deliverance... needed ? *)
                match fuel with
                    | S ful => prog ful msg
                    | 0%nat => skip
                end
    | None => match fuel with
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
    
    prove impure with ping_db.
Qed.

Lemma sn_run `{Provide ix IS, Provide ix IN} {im : impureMonad ix} (fuel : nat) (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (sn_contract) (prog fuel ping)) (ping_sent) tt c)
    : is_legal_state c.
Proof.
    move: run;
    elim: fuel => [|ful EH] run; [|apply/EH].
    {
        run_simpl run; move: run; case x => [m|] run; cleanvert run; run_simpl H3; cleanvert H3.
        - by cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H6.
        done.
    }
        run_simpl run; move: run; case x => [m|] run.
        - by cleanvert run; run_simpl H3; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H5; cleanvert H3; cleanvert H5; cleanvert H3.
        by rewrite -H4.
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
    (* C *) send (im:=im) >>=
    (* N *) deliver >>= fun p => match p with 
        | Some m =>
    (* S *) recv m >> 
    (* S *) sned >>=   
    (* N *) deliver >>= fun p => match p with 
        | Some m' => 
    (* C *) wait m'
        | None => skip
        end    
        | None => skip
        end.

Local Open Scope contract_scope.

Definition cns_contract := c_contract ^ n_contract ^ s_contract.

Lemma cns_respectful `{Provide ix IC, Provide ix IS, Provide ix IN} {im : impureMonad ix}
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cns_contract) (prog)) (init_channel).
Proof.
    prove impure with ping_db;
        case : x0 => // m.
    by prove impure with ping_db;
        case : x2.
Qed.

Lemma cns_run `{Provide ix IC, Provide ix IS, Provide ix IN} (c : CHANNEL)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (cns_contract) (prog)) (init_channel) tt c)
    : is_legal_state c.
Proof.
    run_simpl run; cleanvert run; cleanvert H5; cleanvert H6; cleanvert H5; cleanvert H6.
    move: H7; case : x0 => /= [m|] run; cleanvert run; cleanvert H5 => //.
    
    by cleanvert H6; cleanvert H7; cleanvert H5; cleanvert H6; cleanvert H5; cleanvert H8; cleanvert H5; cleanvert H8; cleanvert H6; cleanvert H8; cleanvert H5; cleanvert H6; cleanvert H7 => //;
        move: H9; case : x3 => //= [m'|] run; cleanvert run; cleanvert H5 => //; cleanvert H6; cleanvert H5; cleanvert H7.
Qed.

    End v2_s.
End V2_M.

(* Definition simple_one_round_fail_prog `{Provide ix IC, Provide ix IS, Provide ix N} {im : impureMonad ix} : im unit :=

(* (a) *)    send (im:=im) >>= fun m => deliver m >>= fun om => match om with | Some _ => recv >> 
(* (b) *)    sned          >>= fun m => deliver m >>= fun om => match om with | Some _ => wait >> skip
    | _ => skip end 
| _ => skip    
    end. *)
