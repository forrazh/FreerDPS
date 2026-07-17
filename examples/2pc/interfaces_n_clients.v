From mathcomp Require Import all_boot ssrnum ssrint.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Impure.

Import FreerFuns.

Generalizable All Variables.

Local Open Scope interface_scope.
Local Open Scope monae_scope.
Local Open Scope ring_scope.

Module InterfaceTwoPhaseCommitNClients.

Section two_phase_commit.

Variable client : eqType.

Inductive role := Coordinator | Client (who : client).

Record update := Update {
  update_client : client;
  update_amount : int
}.

Definition transaction := seq update.
Definition bank_state := client -> int.

Inductive decision := CommitDecision | AbortDecision.

Definition balance_of (state : bank_state) (who : client) : int := state who.

Definition apply_update (state : bank_state) (change : update) : bank_state :=
  fun who =>
    if who == update_client change then
      balance_of state who + update_amount change
    else balance_of state who.

Fixpoint apply_updates (state : bank_state) (changes : transaction)
    : bank_state :=
  if changes is change :: changes' then
    apply_updates (apply_update state change) changes'
  else state.

Definition updates_for (who : client) (changes : transaction) : transaction :=
  filter (fun change => update_client change == who) changes.

Definition valid_updates (state : bank_state) (who : client)
    (changes : transaction) : bool :=
  0 <= balance_of (apply_updates state changes) who.

(* Each interface keeps the communicating roles and protocol data in syntax. *)
Inductive submission_interface : effect :=
| SubmitTransaction (sender receiver : role) (changes : transaction)
    : submission_interface transaction.

Inductive preparation_interface : effect :=
| Prepare (sender receiver : role) (changes : transaction)
    : preparation_interface transaction.

Inductive vote_interface : effect :=
| Vote (sender receiver : role) (vote : bool) : vote_interface bool.

Inductive decision_interface : effect :=
| SelectDecision (sender : role) (receivers : seq role) (choice : decision)
    : decision_interface unit.

Definition two_phase_interface : effect :=
  submission_interface + preparation_interface + vote_interface +
  decision_interface.

Definition send_transaction `{Provide ix submission_interface}
    {im : freerMonad ix} (sender receiver : role) (changes : transaction)
    : im transaction :=
  trigger (SubmitTransaction sender receiver changes).

Definition send_prepare `{Provide ix preparation_interface}
    {im : freerMonad ix} (sender receiver : role) (changes : transaction)
    : im transaction :=
  trigger (Prepare sender receiver changes).

Definition send_vote `{Provide ix vote_interface} {im : freerMonad ix}
    (sender receiver : role) (vote : bool) : im bool :=
  trigger (Vote sender receiver vote).

Definition select `{Provide ix decision_interface} {im : freerMonad ix}
    (sender : role) (receivers : seq role) (choice : decision) : im unit :=
  trigger (SelectDecision sender receivers choice).

Fixpoint prepare_and_vote `{Provide ix preparation_interface}
    `{Provide ix vote_interface} {im : freerMonad ix} (state : bank_state)
    (clients : seq client) (changes : transaction) : im (seq bool) :=
  if clients is who :: clients' then
    send_prepare Coordinator (Client who) (updates_for who changes) >>=
      fun client_changes =>
    send_vote (Client who) Coordinator
      (valid_updates state who client_changes) >>= fun vote =>
    prepare_and_vote state clients' changes >>= fun votes =>
    Ret (vote :: votes)
  else Ret [::].

Definition resulting_state (state : bank_state) (changes : transaction)
    (choice : decision) : bank_state :=
  match choice with
  | CommitDecision => apply_updates state changes
  | AbortDecision => state
  end.

Definition handle_transaction `{Provide ix submission_interface}
    `{Provide ix preparation_interface} `{Provide ix vote_interface}
    `{Provide ix decision_interface} {im : freerMonad ix} (submitter : client)
    (clients : seq client) (state : bank_state) (changes : transaction)
    : im (prod decision bank_state) :=
  send_transaction (Client submitter) Coordinator changes >>= fun submitted =>
  prepare_and_vote state clients submitted >>= fun votes =>
  let choice := if all id votes then CommitDecision else AbortDecision in
  select Coordinator (map Client clients) choice >>= fun _ =>
  Ret (choice, resulting_state state submitted choice).

Definition concrete_handle_transaction (submitter : client)
    (clients : seq client) (state : bank_state) (changes : transaction)
    : freer two_phase_interface (prod decision bank_state) :=
  handle_transaction submitter clients state changes.

(* TODO: Require [uniq clients] and model queues before proving isolation. *)
(* TODO: Add signatures before stating authenticated-vote properties. *)

End two_phase_commit.

End InterfaceTwoPhaseCommitNClients.
