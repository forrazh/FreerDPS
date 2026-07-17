From mathcomp Require Import all_boot ssrnum ssrint.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Impure.

Import FreerFuns.

Generalizable All Variables.

Local Open Scope monae_scope.
Local Open Scope ring_scope.

Module TwoPhaseCommit.

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

Inductive decision := Commit | Abort.

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

Inductive choreography_event : effect :=
| communicate {A : Type} (sender receiver : role) (message : A)
    : choreography_event A
| select_decision (sender : role) (receivers : seq role) (choice : decision)
    : choreography_event unit.

Definition send `{Provide ix choreography_event} {im : freerMonad ix}
    {A : Type} (sender receiver : role) (message : A) : im A :=
  trigger (communicate sender receiver message).

Definition select `{Provide ix choreography_event} {im : freerMonad ix}
    (sender : role) (receivers : seq role) (choice : decision) : im unit :=
  trigger (select_decision sender receivers choice).

Definition resulting_state (state : bank_state) (changes : transaction)
    (choice : decision) : bank_state :=
  match choice with
  | Commit => apply_updates state changes
  | Abort => state
  end.

Definition handle_transaction `{Provide ix choreography_event}
    {im : freerMonad ix} (state : bank_state) (changes : transaction)
    : im (prod decision bank_state) :=
  send Client Coordinator changes >>= fun submitted =>
  send Coordinator Alice (updates_for AliceAccount submitted) >>=
    fun alice_changes =>
  send Coordinator Bob (updates_for BobAccount submitted) >>= fun bob_changes =>
  send Alice Coordinator (valid_updates state AliceAccount alice_changes) >>=
    fun alice_vote =>
  send Bob Coordinator (valid_updates state BobAccount bob_changes) >>=
    fun bob_vote =>
  let choice := if alice_vote && bob_vote then Commit else Abort in
  select Coordinator [:: Alice; Bob] choice >>= fun _ =>
  Ret (choice, resulting_state state submitted choice).

(* TODO: Endpoint-local states and message queues are intentionally omitted. *)

End TwoPhaseCommit.
