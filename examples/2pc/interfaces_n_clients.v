From mathcomp Require Import all_boot ssrnum ssrint.
From monae Require Import preamble hierarchy.
From FreerDPS Require Import Impure Contract Hoare HoareFacts.

(*****************************************************************************
 * This file specifies a finite, sequential two-phase commit choreography    *
 * for an arbitrary list of clients.  The program is interpreted through     *
 * [to_hoare two_phase_contract]; its contract witness stores a bank state    *
 * together with submission, preparation, vote, and decision logs.           *
 *                                                                           *
 * The reusable protocol layer is isolated in [TwoPhaseReusable].  It        *
 * contains the polymorphic request combinators, the [prepare_and_vote] loop, *
 * their caller-side [pre] proofs, their program-specific [post] facts, the   *
 * vote-log invariant, the decision-to-state function, and the generic       *
 * respectful-run coherence theorem.  [Import TwoPhaseReusable] below keeps  *
 * the concrete N-client choreography readable without exporting that        *
 * namespace from [InterfaceTwoPhaseCommitNClients].                          *
 *                                                                           *
 * Safety results:                                                           *
 * - [expected_votes_safe] turns unanimous expected votes into nonnegative   *
 *   final balances for every participating client.                          *
 * - [handle_transaction_safe] states the decision safety property: a commit *
 *   gives every listed client a nonnegative balance, while an abort leaves   *
 *   the bank state unchanged.                                               *
 * - [respectful_run_inv] states that every respectful computation preserves *
 *   [protocol_bank_coherent], i.e., [protocol_balances witness = state].     *
 *                                                                           *
 * The main result is [handle_transaction_correct].  It packages             *
 * [handle_transaction_preI], which proves that the concrete monadic program  *
 * is respectful, with conditional [post] guarantees for decision safety and *
 * final witness coherence.  [handle_transaction_postE] separately           *
 * identifies the program result with [expected_transaction_result].         *
 *                                                                           *
 * Liveness scope: there is no distributed liveness theorem in this file.    *
 * [prepare_and_vote] terminates structurally for a finite [clients] list,    *
 * but the model has no scheduler, queues, failures, retries, or message      *
 * delivery semantics from which eventual commit, abort, or response could   *
 * be proved.  A [pre] proof establishes caller respectfulness, not progress; *
 * every [post] theorem is conditional on a generated postcondition.         *
 *                                                                           *
 * Important assumptions and boundaries:                                    *
 * - [uniq clients] prevents later votes from shadowing earlier votes in the  *
 *   append-at-head vote log.                                                 *
 * - Commit selection requires [positive_votes]; abort selection is always   *
 *   permitted.                                                              *
 * - [valid_signature] is a placeholder equality check, not cryptography.    *
 * - Contract callees return the submitted request payloads.                 *
 * - Protocol requests extend logs but never update [protocol_balances]; the  *
 *   returned [result_state] records the applied transaction separately.      *
 * - No concurrency, isolation, faults, or global message history is         *
 *   modeled.                                                                *
 *****************************************************************************)

Import FreerFuns SpecializedHoareModule.

Generalizable All Variables.

Local Open Scope interface_scope.
Local Open Scope monae_scope.
Local Open Scope ring_scope.

Module InterfaceTwoPhaseCommitNClients.

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
(* Reusable protocol library *)

Module TwoPhaseReusable.

(* ======================================================================== *)
(* Bank update facts *)

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
(* Local contract facts *)

Definition protocol_bank_coherent (witness : protocol_state)
    (state : bank_state) : Prop :=
  protocol_balances witness = state.

Lemma record_submission_coherent (witness : protocol_state)
    (state : bank_state) (tid : transaction_id) (updates : transaction) :
  protocol_bank_coherent witness state ->
  protocol_bank_coherent (record_submission witness tid updates) state.
Proof. by []. Qed.

Lemma record_preparation_coherent (witness : protocol_state)
    (state : bank_state) (tid : transaction_id) (who : client)
    (updates : transaction) :
  protocol_bank_coherent witness state ->
  protocol_bank_coherent
    (record_preparation witness tid who updates) state.
Proof. by []. Qed.

Lemma record_vote_coherent (witness : protocol_state) (state : bank_state)
    (tid : transaction_id) (who : client) (vote : bool) :
  protocol_bank_coherent witness state ->
  protocol_bank_coherent (record_vote witness tid who vote) state.
Proof. by []. Qed.

Lemma record_decision_coherent (witness : protocol_state)
    (state : bank_state) (tid : transaction_id) (choice : decision) :
  protocol_bank_coherent witness state ->
  protocol_bank_coherent (record_decision witness tid choice) state.
Proof. by []. Qed.

Lemma same_transaction_refl (tid : transaction_id) : same_transaction tid tid.
Proof. by rewrite /same_transaction !eqxx. Qed.

Lemma prepared_for_record_preparation (state : protocol_state)
    (tid : transaction_id) (who : client) (updates : transaction) :
  prepared_for (record_preparation state tid who updates) tid who =
    Some updates.
Proof.
by rewrite /prepared_for /record_preparation /= same_transaction_refl eqxx.
Qed.

Lemma vote_for_record_vote (state : protocol_state) (tid : transaction_id)
    (who : client) (vote : bool) :
  vote_for (record_vote state tid who vote) tid who = Some vote.
Proof. by rewrite /vote_for /record_vote /= same_transaction_refl eqxx. Qed.

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

(* Currently unused. *)
Lemma positive_vote_after_record (state : protocol_state) (tid : transaction_id)
    (who : client) :
  positive_votes (record_vote state tid who true) tid [:: Client who].
Proof.
by rewrite /positive_votes vote_for_record_vote.
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

(* ======================================================================== *)
(* Caller-side primitive obligations *)

Lemma send_transaction_preI (witness : protocol_state) (submitter : client)
    (tid : transaction_id) (updates : transaction)
    (submitter_owns_transaction : submitter = transaction_owner tid) :
  pre (to_hoare two_phase_contract
    (send_transaction (Client submitter) Coordinator tid updates
      : freer two_phase_interface transaction)) witness.
Proof.
rewrite /send_transaction to_hoare_request_preE.
rewrite /gen_caller_obligation /=.
exact: submitter_owns_transaction.
Qed.

Lemma send_prepare_preI (witness : protocol_state) (who : client)
    (tid : transaction_id) (updates : transaction)
    (updates_signed : all valid_signature updates) :
  pre (to_hoare two_phase_contract
    (send_prepare Coordinator (Client who) tid updates
      : freer two_phase_interface transaction)) witness.
Proof.
rewrite /send_prepare to_hoare_request_preE.
by rewrite /gen_caller_obligation /=.
Qed.

Lemma send_vote_preI (witness : protocol_state) (state : bank_state)
    (who : client) (tid : transaction_id) (updates : transaction)
    (coherent : protocol_bank_coherent witness state)
    (prepared : prepared_for witness tid who = Some updates) :
  pre (to_hoare two_phase_contract
    (send_vote (Client who) Coordinator tid
      (valid_vote state who updates) : freer two_phase_interface bool))
    witness.
Proof.
rewrite /send_vote to_hoare_request_preE.
rewrite /gen_caller_obligation /=.
exists updates; split=> //.
by rewrite -coherent.
Qed.

Lemma select_abort_preI (witness : protocol_state) (receivers : seq role)
    (tid : transaction_id) :
  pre (to_hoare two_phase_contract
    (select Coordinator receivers tid AbortDecision
      : freer two_phase_interface unit)) witness.
Proof.
rewrite /select to_hoare_request_preE.
by rewrite /gen_caller_obligation /=.
Qed.

Lemma select_commit_preI (witness : protocol_state) (receivers : seq role)
    (tid : transaction_id) (votes_positive :
      positive_votes witness tid receivers) :
  pre (to_hoare two_phase_contract
    (select Coordinator receivers tid CommitDecision
      : freer two_phase_interface unit)) witness.
Proof.
rewrite /select to_hoare_request_preE.
rewrite /gen_caller_obligation /=.
exact: commit_selection_requires_positive_votes votes_positive.
Qed.

(* ======================================================================== *)
(* Primitive postcondition views *)

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
move=> [-> returned_ok].
have -> := preparation_returns witness Coordinator (Client who) tid updates
  returned returned_ok.
by split.
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
move=> [-> returned_ok].
have -> := vote_returns witness (Client who) Coordinator tid vote returned
  returned_ok.
by split.
Qed.

(* ======================================================================== *)
(* N-client voting loop *)

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

Lemma prepare_and_vote_preI (state : bank_state) (clients : seq client)
    (tid : transaction_id) (updates : transaction)
    (witness : protocol_state)
    (coherent : protocol_bank_coherent witness state)
    (updates_signed : all valid_signature updates) :
  pre (to_hoare two_phase_contract
    (prepare_and_vote (im:=freer two_phase_interface)
      state clients tid updates)) witness.
Proof.
elim: clients witness coherent => [|who clients IH] witness coherent //.
rewrite /prepare_and_vote /send_prepare.
apply/to_hoare_impure_preI.
- move: (send_prepare_preI witness who tid (updates_for who updates)
    (updates_for_signed who updates updates_signed)).
  by rewrite /send_prepare to_hoare_request_preE.
move=> client_updates.
rewrite /gen_callee_obligation /gen_witness_update /= => ->.
have prepared_coherent := record_preparation_coherent witness state tid who
  (updates_for who updates) coherent.
rewrite /send_vote /=; split.
- move: (send_vote_preI
    (record_preparation witness tid who (updates_for who updates)) state who
    tid (updates_for who updates) prepared_coherent
    (prepared_for_record_preparation witness tid who
      (updates_for who updates))).
  by rewrite /send_vote to_hoare_request_preE.
move=> vote voted_witness /= [-> ->].
apply: to_hoare_bind_preI.
- apply: IH.
  exact: (record_vote_coherent _ state tid who _ prepared_coherent).
by move=>*; exact: to_hoare_local_preI.
Qed.

(* ======================================================================== *)
(* Voting-loop postconditions and safety *)

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
elim: clients witness votes final_witness=>
  [|who clients IH] witness votes final_witness /=.
  by move=> [<-].
do ! [move=> [? [? [[->]]]]; rewrite /gen_callee_obligation /= => ->].
by rewrite to_hoare_bind_postE; move=> [? [? []]] /IH=> -> [<-].
Qed.

Definition votes_recorded (witness : protocol_state) (tid : transaction_id) :=
  fix recorded (clients : seq client) (votes : seq bool) : Prop :=
    match clients, votes with
    | who :: clients', vote :: votes' =>
        vote_for witness tid who = Some vote /\ recorded clients' votes'
    | [::], [::] => True
    | _, _ => False
    end.

Lemma vote_for_record_preparation (witness : protocol_state)
    (tid : transaction_id) (prepared : client) (updates : transaction)
    (who : client) :
  vote_for (record_preparation witness tid prepared updates) tid who =
  vote_for witness tid who.
Proof. by []. Qed.

Lemma vote_for_record_vote_neq (witness : protocol_state)
    (tid : transaction_id) (recorded who : client) (vote : bool)
    (who_neq : who != recorded) :
  vote_for (record_vote witness tid recorded vote) tid who =
  vote_for witness tid who.
Proof.
move/negPf: who_neq => who_neq.
by rewrite /vote_for /record_vote /= /same_transaction !eqxx /= who_neq.
Qed.

Lemma prepare_and_vote_preserves_vote (state : bank_state)
    (clients : seq client) (tid : transaction_id) (updates : transaction)
    (witness final_witness : protocol_state) (votes : seq bool)
    (who : client) (who_notin : who \notin clients) :
  post (to_hoare two_phase_contract
    (prepare_and_vote (im:=freer two_phase_interface)
      state clients tid updates)) witness votes final_witness ->
  vote_for final_witness tid who = vote_for witness tid who.
Proof.
elim: clients witness votes final_witness who_notin =>
  [|current clients IH] witness votes final_witness who_notin /=.
  by move=> [_ <-].
move: who_notin; rewrite in_cons negb_or => /andP [who_neq who_notin].
move=> [client_updates [prepared_witness [prepare_post continue_post]]].
have prepare_post' : post (to_hoare two_phase_contract
    (send_prepare Coordinator (Client current) tid
      (updates_for current updates) : freer two_phase_interface transaction))
    witness client_updates prepared_witness.
  rewrite /send_prepare to_hoare_request_postE.
  exact: prepare_post.
have prepare_facts := send_prepare_postE witness prepared_witness current tid
  (updates_for current updates) client_updates prepare_post'.
have client_updates_eq := prepare_facts.1.
have prepared_witness_eq := prepare_facts.2.
subst client_updates; subst prepared_witness.
move: continue_post =>
  [vote [voted_witness [vote_post continue_post]]].
have vote_post' : post (to_hoare two_phase_contract
    (send_vote (Client current) Coordinator tid
      (valid_vote state current (updates_for current updates))
      : freer two_phase_interface bool))
    (record_preparation witness tid current (updates_for current updates))
    vote voted_witness.
  rewrite /send_vote to_hoare_request_postE.
  exact: vote_post.
have vote_facts := send_vote_postE _ voted_witness current tid
  (valid_vote state current (updates_for current updates)) vote vote_post'.
have vote_eq := vote_facts.1.
have voted_witness_eq := vote_facts.2.
subst vote; subst voted_witness.
rewrite to_hoare_bind_postE in continue_post.
move: continue_post=> [tail_votes [tail_witness [tail_post ret_post]]].
move: ret_post; rewrite to_hoare_local_postE => -[_ <-].
rewrite (IH _ _ _ who_notin tail_post).
rewrite vote_for_record_vote_neq // vote_for_record_preparation.
Qed.

Lemma prepare_and_vote_votes_recorded (state : bank_state)
    (clients : seq client) (tid : transaction_id) (updates : transaction)
    (witness final_witness : protocol_state) (votes : seq bool)
    (clients_uniq : uniq clients) :
  post (to_hoare two_phase_contract
    (prepare_and_vote (im:=freer two_phase_interface)
      state clients tid updates)) witness votes final_witness ->
  votes_recorded final_witness tid clients votes.
Proof.
elim: clients witness votes final_witness clients_uniq =>
  [|who clients IH] witness votes final_witness /=.
  by move=> _ [<-].
move=> /andP [who_notin clients_uniq].
move=> [? [? [[->]]]].
rewrite /gen_callee_obligation /= => ->.
move=> [? [? [[->]]]].
rewrite /gen_callee_obligation /= => ->.
rewrite to_hoare_bind_postE.
move=> [tail_votes [tail_witness [tail_post]]].
rewrite to_hoare_local_postE => -[<- <-] /=.
split.
- have current_vote_preserved :=
    prepare_and_vote_preserves_vote state clients tid updates _ tail_witness
      tail_votes who who_notin tail_post.
  rewrite current_vote_preserved.
  exact: vote_for_record_vote.
exact: IH _ _ _ clients_uniq tail_post.
Qed.

Lemma votes_recorded_positive (witness : protocol_state)
    (tid : transaction_id) (clients : seq client) (votes : seq bool) :
  votes_recorded witness tid clients votes -> all id votes ->
  positive_votes witness tid (map Client clients).
Proof.
elim: clients votes => [|who clients IH] [|vote votes] //=.
move=> [vote_found votes_found] /andP [vote_positive votes_positive].
rewrite vote_found vote_positive /=.
exact: IH votes_found votes_positive.
Qed.

Lemma prepare_and_vote_positive_votes (state : bank_state)
    (clients : seq client) (tid : transaction_id) (updates : transaction)
    (witness final_witness : protocol_state) (votes : seq bool)
    (clients_uniq : uniq clients) :
  post (to_hoare two_phase_contract
    (prepare_and_vote (im:=freer two_phase_interface)
      state clients tid updates)) witness votes final_witness ->
  all id votes -> positive_votes final_witness tid (map Client clients).
Proof.
move=> votes_post votes_positive.
apply: votes_recorded_positive votes_positive.
exact: prepare_and_vote_votes_recorded clients_uniq votes_post.
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
(* Respectful runs preserve witness/bank coherence *)

Lemma two_phase_request_preserves_coherence {A}
    (event : two_phase_interface A) (witness : protocol_state) (result : A)
    (final_witness : protocol_state) (state : bank_state) :
  pre (to_hoare two_phase_contract
    (trigger event : freer two_phase_interface A)) witness ->
  post (to_hoare two_phase_contract
    (trigger event : freer two_phase_interface A))
    witness result final_witness ->
  protocol_bank_coherent witness state ->
  protocol_bank_coherent final_witness state.
Proof.
move=> _ event_post coherent.
move: result final_witness event_post coherent.
case: event => [[[submitted | prepared] | voted] | selected].
- case: submitted=> sender receiver event_tid event_updates result
    final_witness.
  rewrite to_hoare_request_postE.
  rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _] coherent.
  exact: record_submission_coherent witness state event_tid result coherent.
- case: prepared=> sender receiver event_tid event_updates result
    final_witness.
  case: receiver=> [|receiver_who]; rewrite to_hoare_request_postE.
  + rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _]
      coherent.
    exact: record_preparation_coherent witness state event_tid
      (transaction_owner event_tid) result coherent.
  rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _] coherent.
  exact: record_preparation_coherent witness state event_tid receiver_who
    result coherent.
- case: voted=> sender receiver event_tid event_vote result final_witness.
  case: sender=> [|sender_who]; rewrite to_hoare_request_postE.
  + rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _]
      coherent.
    exact: record_vote_coherent witness state event_tid
      (transaction_owner event_tid) result coherent.
  rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _] coherent.
  exact: record_vote_coherent witness state event_tid sender_who result
    coherent.
case: selected=> sender receivers event_tid choice result final_witness.
rewrite to_hoare_request_postE.
rewrite /gen_witness_update /gen_callee_obligation /= => -[-> _] coherent.
exact: record_decision_coherent witness state event_tid choice coherent.
Qed.

Lemma respectful_run_inv {A} (program : freer two_phase_interface A)
    (witness : protocol_state) (state : bank_state)
    (coherent : protocol_bank_coherent witness state)
    (result : A) (final_witness : protocol_state)
    (program_pre : pre (to_hoare two_phase_contract program) witness)
    (program_post : post (to_hoare two_phase_contract program)
      witness result final_witness) :
  protocol_bank_coherent final_witness state.
Proof.
move: program witness program_pre program_post coherent.
elim=> [local_result | B event continue IH] witness program_pre
    program_post coherent.
- rewrite to_hoare_local_postE in program_post.
  move: program_post=> [_ <-].
  exact: coherent.
rewrite to_hoare_impure_preE in program_pre.
rewrite to_hoare_impure_postE in program_post.
move: program_pre program_post=> [caller next] [event_result [run step]].
apply: (IH event_result
  (gen_witness_update two_phase_contract witness event event_result)).
- exact: next step.
- exact: run.
apply: (two_phase_request_preserves_coherence event witness event_result).
- exact/to_hoare_request_preE.
- exact: to_hoare_request_postI step.
exact: coherent.
Qed.

End TwoPhaseReusable.

Import TwoPhaseReusable.

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

(* The caller-side proof is kept next to the program whose requests it
   justifies. *)

Lemma handle_transaction_preI (submitter : client) (clients : seq client)
    (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates)
    (witness : protocol_state)
    (coherent : protocol_bank_coherent witness state) :
  pre (to_hoare two_phase_contract
    (concrete_handle_transaction submitter clients clients_uniq
      submitter_in_clients tid submitter_owns_transaction state updates
      updates_signed)) witness.
Proof.
rewrite /concrete_handle_transaction /handle_transaction.
rewrite /send_transaction /=; split.
- move: (send_transaction_preI witness submitter tid updates
    submitter_owns_transaction).
  by rewrite /send_transaction to_hoare_request_preE.
move=> submitted submitted_witness.
rewrite /gen_callee_obligation /gen_witness_update /= => -[-> ->].
have submitted_coherent := record_submission_coherent witness state tid
  updates coherent.
apply: to_hoare_bind_preI.
- apply: prepare_and_vote_preI updates_signed.
  exact: submitted_coherent.
move=> votes votes_witness votes_post.
case votes_all: (all id votes).
- rewrite /= /select /=; split.
  + have votes_positive :=
      prepare_and_vote_positive_votes state clients tid updates _
      votes_witness votes clients_uniq votes_post votes_all.
    move: (select_commit_preI votes_witness (map Client clients) tid
      votes_positive).
    by rewrite /select to_hoare_request_preE.
  by move=> returned final_witness.
rewrite /= /select /=; split.
- move: (select_abort_preI votes_witness (map Client clients) tid).
  by rewrite /select to_hoare_request_preE.
by move=> returned final_witness.
Qed.

(* The functional postcondition precedes the safety corollary that uses it. *)

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
rewrite /gen_callee_obligation /= => submit_callee continue_post.
have submitted_eq := submission_returns witness (Client submitter) Coordinator
  tid updates submitted submit_callee.
subst submitted.
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

#[local] Opaque resulting_state.

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
case votes_all: (all id (expected_votes state clients updates)).
- rewrite /= commit_applies_updates.
  move=> who who_in.
  exact: expected_votes_safe state clients updates votes_all who who_in.
exact: abort_preserves_state.
Qed.

(* ======================================================================== *)
(* Main correctness theorem *)

Theorem handle_transaction_correct (submitter : client)
    (clients : seq client) (clients_uniq : uniq clients)
    (submitter_in_clients : submitter \in clients) (tid : transaction_id)
    (submitter_owns_transaction : submitter = transaction_owner tid)
    (state : bank_state) (updates : transaction)
    (updates_signed : all valid_signature updates)
    (witness : protocol_state)
    (coherent : protocol_bank_coherent witness state) :
  pre (to_hoare two_phase_contract
    (concrete_handle_transaction submitter clients clients_uniq
      submitter_in_clients tid submitter_owns_transaction state updates
      updates_signed)) witness /\
  forall (result : transaction_result) (final_witness : protocol_state),
    post (to_hoare two_phase_contract
      (concrete_handle_transaction submitter clients clients_uniq
        submitter_in_clients tid submitter_owns_transaction state updates
        updates_signed)) witness result final_witness ->
    (match result_decision result with
     | CommitDecision =>
         forall who, who \in clients ->
           0 <= balance_of (result_state result) who
     | AbortDecision => result_state result = state
     end) /\
    protocol_bank_coherent final_witness state.
Proof.
have program_pre := handle_transaction_preI submitter clients clients_uniq
  submitter_in_clients tid submitter_owns_transaction state updates
  updates_signed witness coherent.
split=> // result final_witness result_post; split.
- exact: (handle_transaction_safe submitter clients clients_uniq
    submitter_in_clients tid submitter_owns_transaction state updates
    updates_signed witness final_witness result result_post).
exact: (respectful_run_inv
  (concrete_handle_transaction submitter clients clients_uniq
    submitter_in_clients tid submitter_owns_transaction state updates
    updates_signed) witness state coherent result final_witness program_pre
  result_post).
Qed.

(* TODO: Replace [valid_signature] with a cryptographic verification model. *)
(* TODO: Model queues before proving isolation between transaction IDs. *)

End InterfaceTwoPhaseCommitNClients.
