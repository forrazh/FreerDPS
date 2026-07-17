From mathcomp Require Import all_boot ssrnum ssrint.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Impure.

Import FreerFuns.

Generalizable All Variables.

Local Open Scope interface_scope.
Local Open Scope monae_scope.
Local Open Scope ring_scope.

Module InterfaceTwoPhaseCommit.

Inductive role := Client | Coordinator | Alice | Bob.

Inductive account := AliceAccount | BobAccount.

Record update := Update {
  update_account : account;
  update_amount : int
}.

Definition transaction := seq update.

Record bank_state := BankState {
  alice_balance : int;
  bob_balance : int
}.

Inductive decision := CommitDecision | AbortDecision.

Definition balance_of (state : bank_state) (which : account) : int :=
  match which with
  | AliceAccount => alice_balance state
  | BobAccount => bob_balance state
  end.

Definition apply_update (state : bank_state) (change : update) : bank_state :=
  match update_account change with
  | AliceAccount =>
      BankState (alice_balance state + update_amount change) (bob_balance state)
  | BobAccount =>
      BankState (alice_balance state) (bob_balance state + update_amount change)
  end.

Fixpoint apply_updates (state : bank_state) (changes : transaction)
    : bank_state :=
  if changes is change :: changes' then
    apply_updates (apply_update state change) changes'
  else state.

Fixpoint updates_for (which : account) (changes : transaction) : transaction :=
  if changes is change :: changes' then
    if match update_account change, which with
       | AliceAccount, AliceAccount | BobAccount, BobAccount => true
       | AliceAccount, BobAccount | BobAccount, AliceAccount => false
       end then change :: updates_for which changes'
    else updates_for which changes'
  else [::].

Definition valid_updates (state : bank_state) (which : account)
    (changes : transaction) : bool :=
  0 <= balance_of (apply_updates state changes) which.

Definition validates (state : bank_state) (which : account)
    (changes : transaction) : bool :=
  valid_updates state which (updates_for which changes).

(* Each interface is one choreography capability.  Its constructor keeps the
   communicating roles and the protocol data in the syntax. *)
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

Definition resulting_state (state : bank_state) (changes : transaction)
    (choice : decision) : bank_state :=
  match choice with
  | CommitDecision => apply_updates state changes
  | AbortDecision => state
  end.

Definition handle_transaction `{Provide ix submission_interface}
    `{Provide ix preparation_interface} `{Provide ix vote_interface}
    `{Provide ix decision_interface} {im : freerMonad ix} (state : bank_state)
    (changes : transaction) : im (prod decision bank_state) :=
  send_transaction Client Coordinator changes >>= fun submitted =>
  send_prepare Coordinator Alice (updates_for AliceAccount submitted) >>=
    fun alice_changes =>
  send_prepare Coordinator Bob (updates_for BobAccount submitted) >>=
    fun bob_changes =>
  send_vote Alice Coordinator
    (valid_updates state AliceAccount alice_changes) >>=
    fun alice_vote =>
  send_vote Bob Coordinator (valid_updates state BobAccount bob_changes) >>=
    fun bob_vote =>
  let choice := if alice_vote && bob_vote then CommitDecision else AbortDecision in
  select Coordinator [:: Alice; Bob] choice >>= fun _ =>
  Ret (choice, resulting_state state submitted choice).

Definition concrete_handle_transaction (state : bank_state)
    (changes : transaction)
    : freer two_phase_interface (prod decision bank_state) :=
  handle_transaction state changes.

(* TODO: Keep endpoint-local states and message queues in a separate model. *)

End InterfaceTwoPhaseCommit.
