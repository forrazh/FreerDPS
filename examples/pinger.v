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

Definition Id := nat.
Inductive M := ping|pong.

Record MessageHull : UU0 := mkHull {
    msg : M ;
    src : Id ;
    dst : Id
}.

About MessageHull.

Definition msg_eq_dec (m m' : M) : { m = m' } + { ~ m = m' } :=
  ltac:(decide equality).
Definition id_eq_dec (id id' : Id) : { id = id' } + { ~ id = id' } :=
  ltac:(decide equality).

(* Channel contains the current message (optional) and whether it has been dropped or not *)
Definition ChannelState : UU0 := option MessageHull.

Check src.
Module ChannelHelper.

    Definition answer (hull : MessageHull) : MessageHull := match hull with
    | {| msg := m ; src := s ; dst := d |}  => mkHull (match m with
        | ping => pong
        | pong => ping
        end) d s
     end.

    Definition answ_prop (m m' : MessageHull) : Prop := m' = answer m -> m.(msg) <> m'.(msg) /\ m.(src) = m'.(dst) /\ m.(dst) = m'.(src).

    Lemma message_answered (m : MessageHull) : forall m', answ_prop m m'.
    Proof.
        by rewrite /answer;
            case : m ; 
            case => /= s d m' Hanswer;
            rewrite Hanswer.
    Qed.

    Definition answer_through (c : ChannelState) : ChannelState := match c with
    | Some mh => Some $ answer mh
    | None => None
    end.

    Definition update_answer_through (c : ChannelState) (m : MessageHull) (me : Id) : ChannelState :=
    if id_eq_dec m.(src) me then
        None
    else
        match c with
        | Some _ => Some $ answer m
        | None => None
        end.

    Definition look_channels (c c' : ChannelState) (H : MessageHull -> MessageHull -> Prop) : Prop := match c, c' with
    | Some m, Some m' => H m m'
    | None, None => True
    | _, _ => False
    end. 

    Definition channel_inv (c : ChannelState) (H: MessageHull -> MessageHull -> Prop) : Prop := forall c', c' = answer_through c -> look_channels c c' H.


    Lemma message_answered_through_channel (c : ChannelState) : 
        channel_inv c answ_prop.
    Proof. 
        case: c => [?|]; case => //??;
            apply/message_answered.
    Qed.

    Definition channel_empty (c : ChannelState) := match c with 
    | None => True
    | _ => False
    end.

    Definition channel_contains (c : ChannelState) (m : MessageHull) := match c with 
    | Some m' => m = m
    | None => False
    end.

    Lemma channel_does_contain_message : forall m c, c = Some m -> channel_contains c m.
    Proof.
        by move => m c H;
            rewrite H /channel_contains.
    Qed.

    Definition answ_not_me (me you : Id) (m m' : MessageHull) : Prop := me <> you -> m.(dst) = you /\ m.(src) = me -> answ_prop m m'.

    Corollary answer_is_not_me : forall sr ds m m', answ_not_me sr ds m m'.
    Proof.
        move => ??????;
        apply/message_answered.
    Qed.


        (* forall c', c' = answer_through c -> (c = None /\ c' = None) \/ (forall m m', c = Some m /\ c' = Some m' -> answ_prop m m'). *)
    Corollary channel_s_answer_is_not_me (c : ChannelState) : forall sr ds, channel_inv c (answ_not_me sr ds).
    Proof.
            case : c => [?|]??; case => // ??;
                apply/answer_is_not_me.
    Qed.


    Inductive legal_transitions : ChannelState -> ChannelState -> Prop := 
    | request_echo (s d : Id) : legal_transitions None (Some $ mkHull ping s d)
    | answer_echo (s d : Id) : legal_transitions (Some $ mkHull ping s d) (Some $ mkHull pong d s)
    | reset_echo (s d : Id) : legal_transitions (Some $ mkHull pong s d) None.

    (* Definition localCoh (n: nid) := [Pred l | if n == cn then ∃(r: round) (s: CState) (log: Log), l = st ↦→ (r, s) ⊎ lg ↦→ log else if n ∈ pts  then ∃(r: round) (s: PState) (log: Log), l = st ↦→ (r, s) ⊎ lg ↦→ log else True]. *)
End ChannelHelper.

Import ChannelHelper.

Module CLIENT_M.
    Section client_s.

Print interface.
Inductive IC : interface :=
| SEND : MessageHull -> IC unit
| WAIT : IC MessageHull.

Definition send `{Provide ix IC} {im : impureMonad ix} (m : MessageHull) := trigger (im:=im) (inj_p $ SEND m).
Definition wait `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ WAIT).

Definition C `{Provide ix IC} {im : impureMonad ix} (me you : Id) := 
    send (im:=im) (mkHull ping me you) >> wait.

Check make_contract.

(* 
make_contract
     : forall (i : interface) (Ω : UU0),
(Ω -> forall α : UU0, i α -> α -> Ω) ->
(Ω -> forall α : UU0, i α -> Prop) ->
(Ω -> forall α : UU0, i α -> α -> Prop) ->
contract i Ω
*)



Definition client_update :=
  fun (c : ChannelState) (α : Type) (e : IC α) (x : α) =>
    match e with
    | WAIT => c 
    | SEND m => Some m
    end.

    Check client_update. 
(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equivalent to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Inductive o_caller_store (c : ChannelState) : forall X, IC X -> Prop :=
| send_o_caller (m' : MessageHull) (coh : c = None): o_caller_store c (SEND m').


Inductive o_callee_store (c : ChannelState) : forall (α : Type), IC α -> α -> Prop :=
| get_o_callee (m : MessageHull) (equ : c = None \/ c = Some m): o_callee_store c WAIT m
| put_o_callee (m' :  MessageHull) (u : unit) : o_callee_store c (SEND m') u.

(** The actual contract can therefore be defined as follows: *)

Definition c_contract : contract (IC) ChannelState :=
  {| witness_update := client_update
  ;  caller_obligation := no_caller_obligation
  ;  callee_obligation := o_callee_store
  |}.


Lemma client_run `{Provide ix IC} {im : impureMonad ix} (m : MessageHull) (final_state: ChannelState) (me you : Id)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (c_contract) (C me you)) (None) m final_state) 
    : channel_contains final_state m. 
    (* (mkHull ping me you). *)
Proof.
    run_simpl run;
        cleanvert H1;
        cleanvert run;
        cleanvert H1;
        cleanvert H2; cleanvert H3;
        cleanvert H1.
    by move : H2; rewrite /gen_callee_obligation/gen_witness_update;
        case : (proj_p (inj_p WAIT)) => //= e H2;
        inversion H2; rewrite /channel_contains /client_update /=;case e.

Qed.   
    End client_s.
End CLIENT_M.

(* ------------------------------------------------------------------------------------ *)

Module SERVER_M.
    Section server_s.
Inductive IS : interface :=
| RECV : IS MessageHull
| SNED : MessageHull -> IS unit.

Definition sned `{Provide ix IS} {im : impureMonad ix} (m : MessageHull) := trigger (im:=im) (inj_p $ SNED m).
Definition recv `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ RECV).

(**
 * Here we model a recursive server (using fuel as functions must terminate).
 * For convenience purposes, a message is passed to all rounds.
 *)
Fixpoint S_ `{Provide ix IS} {im : impureMonad ix} (fuel : nat) : im unit := (*fun (X : im T) => *) 
    recv (im:=im) >>= 
    sned >> 
    match fuel with
        | S ful => S_ ful
        | 0%nat => skip
    end.

Check answer_through.
Print answer_through.

Definition s_step (me : Id) (c : ChannelState) : forall X : UU0, IS X -> X -> ChannelState :=
fun X e x => 
match e with 
| RECV => c
| SNED m => update_answer_through c m me
end.
(* move => ? e ?; inversion e;subst; *)
    (* apply/update_msg/c; [apply/ping | apply/pong]. *)
(* Defined. *)

(* Inductive s_o_caller (you me : Id) (curr : ChannelState) : forall X : UU0, IS X -> Prop := 
| RECV_O (equ : curr = None \/ (forall m, curr = Some m -> m.(src) = you /\ m.(dst) = me)) : s_o_caller you me curr (RECV)
| SNED_O (m : MessageHull) : s_o_caller you me curr (SNED m).
Hint Constructors s_o_caller : ping_db. *)

Variable c : ChannelState.
(* Check (channel_s_answer_is_not_me (c:=c) _ _ : Prop). *)
Check channel_inv. 

Inductive s_o_callee (you me : Id) (curr: ChannelState) : forall X : UU0, IS X -> X -> Prop :=
| O_RECV (m : MessageHull) (equ : curr = None \/ (curr = Some m))  : s_o_callee you me curr (RECV) m
| O_SNED (m' :  MessageHull) (u : unit) : s_o_callee you me curr (SNED m') tt.

Hint Constructors s_o_callee : ping_db.

(* Definition s_contract (you me : Id):= make_contract (s_step me) (s_o_caller you me) (s_o_callee you me). *)
Definition s_contract (you me : Id):= make_contract (s_step me) (no_caller_obligation) (s_o_callee you me).

Lemma server_respectful_no_msg `{Provide ix IS} {im : impureMonad ix} (fuel : nat) (you me : Id)
        : pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract you me) (S_ fuel)) None.
Proof.
    move : you me; elim : fuel => [|ful EH] you me; prove impure with ping_db; rewrite /update_answer_through // if_same ;
        apply/EH.
Qed.

Lemma server_respectful_pinged `{Provide ix IS} {im : impureMonad ix} (fuel : nat) (you me : Id) initial
        : you <> me -> pre (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract you me) (S_ fuel)) initial.
Proof.
    move : you me initial; elim : fuel => [|ful EH] you me initial Hdiff; prove impure with ping_db. 
    apply/EH; prove impure with ping_db.
Qed.

Lemma server_run_empty_forever `{Provide ix IS} {im : impureMonad ix} (final_state : ChannelState) (fuel : nat) (you me : Id)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract you me) (S_ fuel)) None tt final_state) 
    :  you <> me -> channel_empty final_state.
Proof.
    by move : run; 
        elim : fuel => [| ful EH] run Hdiff; [| apply/EH];
        run_simpl run; cleanvert H1; cleanvert equ => //;
        cleanvert run; cleanvert H2; cleanvert H3 ; cleanvert H2;
        move : H4 H3; rewrite /gen_witness_update/gen_callee_obligation/channel_empty; case : (proj_p (inj_p (SNED x))) => [e|] //= H4 H3;
        [cleanvert H4 | by cleanvert H4 | move : H4];
        rewrite /s_step/update_answer_through; case e => //m; rewrite if_same.
Qed.

Lemma server_run `{Provide ix IS} {im : impureMonad ix} (m m': MessageHull) (initial_state final_state : ChannelState) (fuel : nat) (you me : Id)
        (run : post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) (s_contract you me) (S_ fuel)) initial_state tt final_state) 
    :  you <> me -> channel_contains final_state m' \/ channel_empty final_state.
Proof.
    move : run; 
        elim : fuel => [|ful EH] run Hdiff; 
            (* [| apply/EH]; *)
        (* rework to put only 'unroll_post' *)
        run_simpl run; 
            cleanvert H1; cleanvert run; cleanvert H1; 
            run_simpl H2; cleanvert H1.
        - by cleanvert equ; cleanvert H2; rewrite /update_answer_through ?if_same /channel_contains //=; 
            case : x => ? s ? /=; case (is_left (id_eq_dec s me)) => //; right.

        cleanvert equ; apply/EH => //; move : H2; rewrite /update_answer_through ?if_same //.

        (* This is a trap. v *)
        elim ful => [| fu EH'] H2.
        - cleanvert H2; cleanvert H1; cleanvert H2; cleanvert H3; cleanvert H2; cleanvert H3; cleanvert H4; cleanvert H3; cleanvert H2; cleanvert H1; move : H3 H2; rewrite /gen_callee_obligation /gen_witness_update; case : (proj_p (inj_p (inj_p (inj_p (SNED x0))))) => [e|]; case : (proj_p (inj_p RECV)) => [e'|]; case (is_left (id_eq_dec (src x) me)) => H3 H2; rewrite /witness_update.

        (* inversion H2; inversion H3.
        ; move : H2; rewrite /update_answer_through ?if_same //.
            case x => ? s ? /=;
            case (is_left (id_eq_dec s me)) => //= H2.
        - admit.
        apply/H2.

        cleanvert H2.

        move : H1 H2 EH; case : x => /= content src dst [Hl [Hy Hm]]. move : Hl; rewrite Hy Hm => Hl H2; apply;
        rewrite Hl; move : H2.
        elim : ful => /= [|fu EH'] H2.
        cleanvert H2 ; cleanvert H1  ; cleanvert H2; cleanvert H3; cleanvert H2; cleanvert H3; cleanvert H4; cleanvert H2; cleanvert H1.
        move : H4 H2.
        rewrite /gen_callee_obligation/gen_witness_update.
        case : (proj_p (inj_p RECV)) => //= [e|]; case : (proj_p (inj_p (SNED x))) => //= [e'|] H4 H2.
        inversion H2 => //=. inversion equ => //=.
        - cleanvert equ; cleanvert H6; cleanvert H5; cleanvert H1 => //=.
            exists (answer x); exists (Some  x);
            split => //=.
            cleanvert H7; cleanvert H1 => //=.
        specialize (H1 me you); case : H1 => //= H1; case =>??. *)
Admitted.
(* Qed.     *)

End server_s.


