From mathcomp Require Import all_boot ssrnum ssrint.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Impure Contract Hoare HoareFacts.

Import FreerFuns SpecializedHoareModule.

Generalizable All Variables.

Local Open Scope interface_scope.
Local Open Scope monae_scope.
Local Open Scope ring_scope.

Module InterfaceTwoPhaseCommitNClients.

Section two_phase_commit.

(* ======================================================================== *)
(* Protocol data model *)

Definition client := nat.

Inductive role := Coordinator | Client (who : client).

Record transaction_id := TransactionId {
  transaction_owner : client;
  transaction_nonce : nat
}.

Record signed_update := SignedUpdate {
  signed_account : client;
  signed_amount : int;
  signed_by : client
}.

Definition transaction := seq signed_update.
Definition bank_state := client -> int.

Inductive decision := CommitDecision | AbortDecision.

(* ======================================================================== *)
(* Bank updates and validation *)

Definition balance_of (state : bank_state) (who : client) : int := state who.

Definition valid_signature (signed : signed_update) : bool :=
  signed_by signed == signed_account signed.

Definition apply_update (state : bank_state) (signed : signed_update)
    : bank_state :=
  fun who =>
    if who == signed_account signed then
      balance_of state who + signed_amount signed
    else balance_of state who.

Fixpoint apply_updates (state : bank_state) (updates : transaction)
    : bank_state :=
  if updates is signed :: updates' then
    apply_updates (apply_update state signed) updates'
  else state.

Definition updates_for (who : client) (updates : transaction) : transaction :=
  filter (fun signed => signed_account signed == who) updates.

Definition valid_updates (state : bank_state) (who : client)
    (updates : transaction) : bool :=
  0 <= balance_of (apply_updates state updates) who.

Definition valid_vote (state : bank_state) (who : client)
    (updates : transaction) : bool :=
  all valid_signature updates && valid_updates state who updates.

Lemma apply_updates_balance_congr (left right : bank_state)
    (updates : transaction) (who : client) :
  balance_of left who = balance_of right who ->
  balance_of (apply_updates left updates) who =
  balance_of (apply_updates right updates) who.
Proof.
elim: updates left right => [|signed updates IH] left right //=.
move=> balances_equal.
apply: IH.
move: balances_equal; rewrite /balance_of => balances_equal.
rewrite /apply_update /balance_of.
case: (who == signed_account signed) => /=.
  by rewrite balances_equal.
exact: balances_equal.
Qed.

Lemma apply_updates_for_balance (state : bank_state) (updates : transaction)
    (who : client) :
  balance_of (apply_updates state (updates_for who updates)) who =
  balance_of (apply_updates state updates) who.
Proof.
elim: updates state => [|signed updates IH] state //=.
rewrite /updates_for /=.
case account_eq: (signed_account signed == who).
  exact: IH.
rewrite IH.
apply: apply_updates_balance_congr.
by rewrite /apply_update /balance_of eq_sym account_eq.
Qed.

(* ======================================================================== *)
(* Protocol interfaces *)

(* Each interface keeps the communicating roles and protocol data in syntax. *)
Inductive submission_interface : effect :=
| SubmitTransaction (sender receiver : role) (tid : transaction_id)
    (updates : transaction)
    : submission_interface transaction.

Inductive preparation_interface : effect :=
| Prepare (sender receiver : role) (tid : transaction_id)
    (updates : transaction)
    : preparation_interface transaction.

Inductive vote_interface : effect :=
| Vote (sender receiver : role) (tid : transaction_id) (vote : bool)
    : vote_interface bool.

Inductive decision_interface : effect :=
| SelectDecision (sender : role) (receivers : seq role) (tid : transaction_id)
    (choice : decision)
    : decision_interface unit.

Definition two_phase_interface : effect :=
  submission_interface + preparation_interface + vote_interface +
  decision_interface.

(* ======================================================================== *)
(* Local contract witness *)

Definition submitted_entry := prod transaction_id transaction.
Definition prepared_entry := prod transaction_id (prod client transaction).
Definition vote_entry := prod transaction_id (prod client bool).
Definition decision_entry := prod transaction_id decision.

Record protocol_state := ProtocolState {
  protocol_balances : bank_state;
  submitted_log : seq submitted_entry;
  prepared_log : seq prepared_entry;
  vote_log : seq vote_entry;
  decision_log : seq decision_entry
}.

Definition same_transaction (left right : transaction_id) : bool :=
  (transaction_owner left == transaction_owner right) &&
  (transaction_nonce left == transaction_nonce right).

Definition record_submission (state : protocol_state) (tid : transaction_id)
    (updates : transaction) : protocol_state :=
  ProtocolState (protocol_balances state)
    ((tid, updates) :: submitted_log state) (prepared_log state)
    (vote_log state) (decision_log state).

Definition record_preparation (state : protocol_state) (tid : transaction_id)
    (who : client) (updates : transaction) : protocol_state :=
  ProtocolState (protocol_balances state) (submitted_log state)
    ((tid, (who, updates)) :: prepared_log state) (vote_log state)
    (decision_log state).

Definition record_vote (state : protocol_state) (tid : transaction_id)
    (who : client) (vote : bool) : protocol_state :=
  ProtocolState (protocol_balances state) (submitted_log state)
    (prepared_log state) ((tid, (who, vote)) :: vote_log state)
    (decision_log state).

Definition record_decision (state : protocol_state) (tid : transaction_id)
    (choice : decision) : protocol_state :=
  ProtocolState (protocol_balances state) (submitted_log state)
    (prepared_log state) (vote_log state)
    ((tid, choice) :: decision_log state).

Fixpoint find_prepared (tid : transaction_id) (who : client)
    (entries : seq prepared_entry) : option transaction :=
  if entries is (other_tid, (other_who, updates)) :: entries' then
    if same_transaction tid other_tid && (who == other_who) then Some updates
    else find_prepared tid who entries'
  else None.

Definition prepared_for (state : protocol_state) (tid : transaction_id)
    (who : client) : option transaction :=
  find_prepared tid who (prepared_log state).

Fixpoint find_vote (tid : transaction_id) (who : client)
    (entries : seq vote_entry) : option bool :=
  if entries is (other_tid, (other_who, vote)) :: entries' then
    if same_transaction tid other_tid && (who == other_who) then Some vote
    else find_vote tid who entries'
  else None.

Definition vote_for (state : protocol_state) (tid : transaction_id)
    (who : client) : option bool :=
  find_vote tid who (vote_log state).

Fixpoint positive_votes (state : protocol_state) (tid : transaction_id)
    (receivers : seq role) : bool :=
  if receivers is Client who :: receivers' then
    if vote_for state tid who is Some vote then
      vote && positive_votes state tid receivers'
    else false
  else if receivers is Coordinator :: receivers' then
    positive_votes state tid receivers'
  else true.

Definition submission_step (state : protocol_state) : forall X,
    submission_interface X -> X -> protocol_state :=
  fun X event =>
    match event in submission_interface result_type
      return result_type -> protocol_state with
    | SubmitTransaction _ _ tid _ =>
        fun returned => record_submission state tid returned
    end.

Definition submission_caller (state : protocol_state) : forall X,
    submission_interface X -> Prop :=
  fun X event =>
    match event with
    | SubmitTransaction (Client owner) Coordinator tid _ =>
        owner = transaction_owner tid
    | _ => False
    end.

Definition submission_callee (state : protocol_state) : forall X,
    submission_interface X -> X -> Prop :=
  fun X event =>
    match event in submission_interface result_type
      return result_type -> Prop with
    | SubmitTransaction _ _ _ updates => fun returned => returned = updates
    end.

Definition submission_contract : contract submission_interface protocol_state :=
  make_contract submission_step submission_caller submission_callee.

Definition preparation_step (state : protocol_state) : forall X,
    preparation_interface X -> X -> protocol_state :=
  fun X event =>
    match event in preparation_interface result_type
      return result_type -> protocol_state with
    | Prepare _ (Client who) tid _ =>
        fun returned => record_preparation state tid who returned
    | Prepare _ _ tid _ =>
        fun returned =>
          record_preparation state tid (transaction_owner tid) returned
    end.

Definition preparation_caller (state : protocol_state) : forall X,
    preparation_interface X -> Prop :=
  fun X event =>
    match event with
    | Prepare Coordinator (Client _) _ updates => all valid_signature updates
    | _ => False
    end.

Definition preparation_callee (state : protocol_state) : forall X,
    preparation_interface X -> X -> Prop :=
  fun X event =>
    match event in preparation_interface result_type
      return result_type -> Prop with
    | Prepare _ _ _ updates => fun returned => returned = updates
    end.

Definition preparation_contract
    : contract preparation_interface protocol_state :=
  make_contract preparation_step preparation_caller preparation_callee.

Definition vote_step (state : protocol_state) : forall X, vote_interface X -> X
    -> protocol_state :=
  fun X event =>
    match event in vote_interface result_type
      return result_type -> protocol_state with
    | Vote (Client who) _ tid _ =>
        fun returned => record_vote state tid who returned
    | Vote _ _ tid _ =>
        fun returned => record_vote state tid (transaction_owner tid) returned
    end.

Definition vote_caller (state : protocol_state) : forall X, vote_interface X
    -> Prop :=
  fun X event =>
    match event with
    | Vote (Client who) Coordinator tid vote =>
        exists updates, prepared_for state tid who = Some updates /\
          vote = valid_vote (protocol_balances state) who updates
    | _ => False
    end.

Definition vote_callee (state : protocol_state) : forall X, vote_interface X
    -> X -> Prop :=
  fun X event =>
    match event in vote_interface result_type return result_type -> Prop with
    | Vote _ _ _ vote => fun returned => returned = vote
    end.

Definition vote_contract : contract vote_interface protocol_state :=
  make_contract vote_step vote_caller vote_callee.

Definition decision_step (state : protocol_state) : forall X,
    decision_interface X -> X -> protocol_state :=
  fun X event =>
    match event in decision_interface result_type
      return result_type -> protocol_state with
    | SelectDecision _ _ tid choice => fun _ => record_decision state tid choice
    end.

Definition decision_caller (state : protocol_state) : forall X,
    decision_interface X -> Prop :=
  fun X event =>
    match event with
    | SelectDecision Coordinator receivers tid CommitDecision =>
        positive_votes state tid receivers
    | SelectDecision Coordinator _ _ AbortDecision => True
    | _ => False
    end.

Definition decision_callee (state : protocol_state) : forall X,
    decision_interface X -> X -> Prop :=
  fun X event =>
    match event in decision_interface result_type
      return result_type -> Prop with
    | SelectDecision _ _ _ _ => fun returned => returned = tt
    end.

Definition decision_contract : contract decision_interface protocol_state :=
  make_contract decision_step decision_caller decision_callee.

(* ======================================================================== *)
(* Combined protocol contract *)

Definition two_phase_step (state : protocol_state) : forall X,
    two_phase_interface X -> X -> protocol_state :=
  fun X event returned =>
    match event with
    | in_left (in_left (in_left submitted)) =>
        submission_step state _ submitted returned
    | in_left (in_left (in_right prepared)) =>
        preparation_step state _ prepared returned
    | in_left (in_right vote) => vote_step state _ vote returned
    | in_right selected => decision_step state _ selected returned
    end.

Definition two_phase_caller (state : protocol_state) : forall X,
    two_phase_interface X -> Prop :=
  fun X event =>
    match event with
    | in_left (in_left (in_left submitted)) =>
        submission_caller state _ submitted
    | in_left (in_left (in_right prepared)) =>
        preparation_caller state _ prepared
    | in_left (in_right vote) => vote_caller state _ vote
    | in_right selected => decision_caller state _ selected
    end.

Definition two_phase_callee (state : protocol_state) : forall X,
    two_phase_interface X -> X -> Prop :=
  fun X event returned =>
    match event with
    | in_left (in_left (in_left submitted)) =>
        submission_callee state _ submitted returned
    | in_left (in_left (in_right prepared)) =>
        preparation_callee state _ prepared returned
    | in_left (in_right vote) => vote_callee state _ vote returned
    | in_right selected => decision_callee state _ selected returned
    end.

Definition two_phase_contract : contract two_phase_interface protocol_state :=
  make_contract two_phase_step two_phase_caller two_phase_callee.

(* ======================================================================== *)
(* Local contract facts *)

Lemma same_transaction_refl (tid : transaction_id) : same_transaction tid tid.
Proof. by rewrite /same_transaction !eqxx. Qed.

Lemma prepared_for_record_preparation (state : protocol_state)
    (tid : transaction_id) (who : client) (updates : transaction) :
  prepared_for (record_preparation state tid who updates) tid who =
    Some updates.
Proof.
by rewrite /prepared_for /record_preparation /= /same_transaction !eqxx.
Qed.

Lemma vote_for_record_vote (state : protocol_state) (tid : transaction_id)
    (who : client) (vote : bool) :
  vote_for (record_vote state tid who vote) tid who = Some vote.
Proof. by rewrite /vote_for /record_vote /= /same_transaction !eqxx. Qed.

Lemma updates_for_signed (who : client) (updates : transaction) :
  all valid_signature updates -> all valid_signature (updates_for who updates).
Proof.
elim: updates => [|signed updates IH] //=.
move=> /andP [signed_valid updates_valid].
rewrite /updates_for /=.
case: (signed_account signed == who) => //=.
  by rewrite signed_valid IH.
by rewrite IH.
Qed.

Lemma positive_vote_after_record (state : protocol_state) (tid : transaction_id)
    (who : client) :
  positive_votes (record_vote state tid who true) tid [:: Client who].
Proof.
by rewrite /positive_votes /vote_for /record_vote /= /same_transaction !eqxx.
Qed.

Lemma submission_returns (state : protocol_state) (sender receiver : role)
    (tid : transaction_id) (updates returned : transaction) :
  callee_obligation submission_contract state
    (SubmitTransaction sender receiver tid updates) returned ->
  returned = updates.
Proof. by []. Qed.

Lemma preparation_returns (state : protocol_state) (sender receiver : role)
    (tid : transaction_id) (updates returned : transaction) :
  callee_obligation preparation_contract state
    (Prepare sender receiver tid updates) returned ->
  returned = updates.
Proof. by []. Qed.

Lemma vote_returns (state : protocol_state) (sender receiver : role)
    (tid : transaction_id) (vote returned : bool) :
  callee_obligation vote_contract state (Vote sender receiver tid vote)
    returned ->
  returned = vote.
Proof. by []. Qed.

Lemma commit_selection_requires_positive_votes (state : protocol_state)
    (receivers : seq role) (tid : transaction_id) :
  caller_obligation decision_contract state
    (SelectDecision Coordinator receivers tid CommitDecision) ->
  positive_votes state tid receivers.
Proof. by []. Qed.

(* ======================================================================== *)
(* Reusable protocol components *)

(* These helpers and the voting loop are polymorphic in any composite that
   provides the corresponding local 2PC interface. *)
Definition send_transaction `{Provide ix submission_interface}
    {im : freerMonad ix} (sender receiver : role) (tid : transaction_id)
    (updates : transaction) : im transaction :=
  trigger (SubmitTransaction sender receiver tid updates).

Definition send_prepare `{Provide ix preparation_interface}
    {im : freerMonad ix} (sender receiver : role) (tid : transaction_id)
    (updates : transaction) : im transaction :=
  trigger (Prepare sender receiver tid updates).

Definition send_vote `{Provide ix vote_interface} {im : freerMonad ix}
    (sender receiver : role) (tid : transaction_id) (vote : bool) : im bool :=
  trigger (Vote sender receiver tid vote).

Definition select `{Provide ix decision_interface} {im : freerMonad ix}
    (sender : role) (receivers : seq role) (tid : transaction_id)
    (choice : decision) : im unit :=
  trigger (SelectDecision sender receivers tid choice).

Lemma send_prepare_postE (witness final_witness : protocol_state)
    (who : client) (tid : transaction_id) (updates returned : transaction) :
  post (to_hoare two_phase_contract
    (send_prepare Coordinator (Client who) tid updates
      : freer two_phase_interface transaction))
    witness returned final_witness ->
  returned = updates /\
  final_witness = record_preparation witness tid who updates.
Proof.
rewrite /send_prepare to_hoare_request_postE.
rewrite /gen_witness_update /gen_callee_obligation /=.
by move=> [-> ->].
Qed.

Lemma send_vote_postE (witness final_witness : protocol_state)
    (who : client) (tid : transaction_id) (vote returned : bool) :
  post (to_hoare two_phase_contract
    (send_vote (Client who) Coordinator tid vote
      : freer two_phase_interface bool))
    witness returned final_witness ->
  returned = vote /\ final_witness = record_vote witness tid who vote.
Proof.
rewrite /send_vote to_hoare_request_postE.
rewrite /gen_witness_update /gen_callee_obligation /=.
by move=> [-> ->].
Qed.

Fixpoint prepare_and_vote `{Provide ix preparation_interface}
    `{Provide ix vote_interface} {im : freerMonad ix} (state : bank_state)
    (clients : seq client) (tid : transaction_id) (updates : transaction)
    : im (seq bool) :=
  if clients is who :: clients' then
    send_prepare Coordinator (Client who) tid (updates_for who updates) >>=
      fun client_updates =>
    send_vote (Client who) Coordinator tid
      (valid_vote state who client_updates) >>= fun vote =>
    prepare_and_vote state clients' tid updates >>= fun votes =>
    Ret (vote :: votes)
  else Ret [::].

Definition expected_votes (state : bank_state) (clients : seq client)
    (updates : transaction) : seq bool :=
  map (fun who => valid_vote state who (updates_for who updates)) clients.

Lemma prepare_and_vote_postE (state : bank_state) (clients : seq client)
    (tid : transaction_id) (updates : transaction)
    (witness final_witness : protocol_state) (votes : seq bool) :
  post (to_hoare two_phase_contract
    (prepare_and_vote (im:=freer two_phase_interface)
      state clients tid updates)) witness votes final_witness ->
  votes = expected_votes state clients updates.
Proof.
elim: clients witness votes final_witness =>
  [|who clients IH] witness votes final_witness /=.
  by move=> [<-].
move=> [? [? [[->]]]];
  rewrite /gen_callee_obligation /= => ->.
move=> [? [? [[->]]]];
  rewrite /gen_callee_obligation /= => ->.
rewrite to_hoare_bind_postE.
by move=> [? [? []]] /IH=> -> [<-].
Qed.

Lemma expected_votes_safe (state : bank_state) (clients : seq client)
    (updates : transaction) :
  all id (expected_votes state clients updates) ->
  forall who, who \in clients ->
    0 <= balance_of (apply_updates state updates) who.
Proof.
rewrite /expected_votes all_map => /allP votes_valid who who_in.
move: (votes_valid who who_in).
rewrite /valid_vote => /andP [_].
by rewrite /valid_updates apply_updates_for_balance.
Qed.

(* Reusable: this decision-to-state function is independent of the effect
   composite and is used by every 2PC entry point in this example. *)
Definition resulting_state (state : bank_state) (updates : transaction)
    (choice : decision) : bank_state :=
  match choice with
  | CommitDecision => apply_updates state updates
  | AbortDecision => state
  end.

Lemma abort_preserves_state (state : bank_state) (updates : transaction) :
  resulting_state state updates AbortDecision = state.
Proof. by []. Qed.

Lemma commit_applies_updates (state : bank_state) (updates : transaction) :
  resulting_state state updates CommitDecision = apply_updates state updates.
Proof. by []. Qed.

(* ======================================================================== *)
(* N-client transaction choreography *)

Record transaction_result := TransactionResult {
  result_id : transaction_id;
  result_decision : decision;
  result_state : bank_state
}.

Definition handle_transaction `{Provide ix submission_interface}
    `{Provide ix preparation_interface} `{Provide ix vote_interface}
    `{Provide ix decision_interface} {im : freerMonad ix} (submitter : client)
    (clients : seq client) (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates) : im transaction_result :=
  send_transaction (Client submitter) Coordinator tid updates >>=
    fun submitted =>
  prepare_and_vote state clients tid submitted >>= fun votes =>
  let choice := if all id votes then CommitDecision else AbortDecision in
  select Coordinator (map Client clients) tid choice >>= fun _ =>
  Ret (TransactionResult tid choice (resulting_state state submitted choice)).

Definition concrete_handle_transaction (submitter : client)
    (clients : seq client) (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates)
    : freer two_phase_interface transaction_result :=
  handle_transaction submitter clients clients_uniq submitter_in_clients tid
    submitter_owns_transaction state updates updates_signed.

Definition expected_transaction_result (tid : transaction_id)
    (state : bank_state) (clients : seq client) (updates : transaction)
    : transaction_result :=
  let votes := expected_votes state clients updates in
  let choice := if all id votes then CommitDecision else AbortDecision in
  TransactionResult tid choice (resulting_state state updates choice).

Lemma handle_transaction_postE (submitter : client) (clients : seq client)
    (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates)
    (witness final_witness : protocol_state) (result : transaction_result) :
  post (to_hoare two_phase_contract
    (concrete_handle_transaction submitter clients clients_uniq
      submitter_in_clients tid submitter_owns_transaction state updates
      updates_signed)) witness result final_witness ->
  result = expected_transaction_result tid state clients updates.
Proof.
rewrite /concrete_handle_transaction /handle_transaction.
rewrite to_hoare_impure_postE.
move=> [submitted [continue_post submit_callee]].
move: submit_callee continue_post.
rewrite /gen_callee_obligation /= => -> continue_post.
rewrite to_hoare_bind_postE in continue_post.
move: continue_post => [votes [after_votes [votes_post continue_post]]].
move: continue_post.
move/prepare_and_vote_postE: votes_post => -> continue_post.
rewrite /expected_transaction_result.
case votes_all: (all id (expected_votes state clients updates)).
  move: continue_post => [returned [after_select
    [[after_select_eq returned_eq] ret_post]]].
  move: ret_post => [ret_eq final_eq].
  rewrite votes_all /= in ret_eq.
  exact: esym ret_eq.
move: continue_post => [returned [after_select
  [[after_select_eq returned_eq] ret_post]]].
move: ret_post => [ret_eq final_eq].
rewrite votes_all /= in ret_eq.
exact: esym ret_eq.
Qed.

Lemma handle_transaction_safe (submitter : client) (clients : seq client)
    (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates)
    (witness final_witness : protocol_state) (result : transaction_result) :
  post (to_hoare two_phase_contract
    (concrete_handle_transaction submitter clients clients_uniq
      submitter_in_clients tid submitter_owns_transaction state updates
      updates_signed)) witness result final_witness ->
  match result_decision result with
  | CommitDecision =>
      forall who, who \in clients -> 0 <= balance_of (result_state result) who
  | AbortDecision => result_state result = state
  end.
Proof.
move=> execution_post.
move/handle_transaction_postE: execution_post => ->.
rewrite /expected_transaction_result.
case votes_all: (all id (expected_votes state clients updates)) => /=.
  move=> who who_in.
  exact: expected_votes_safe state clients updates votes_all who who_in.
by [].
Qed.

(* TODO: Replace [valid_signature] with a cryptographic verification model. *)
(* TODO: Model queues before proving isolation between transaction IDs. *)

End two_phase_commit.

End InterfaceTwoPhaseCommitNClients.
