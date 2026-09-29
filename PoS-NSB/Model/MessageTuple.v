From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Messages
     Parameters.
From HB Require Import structures.
From RecordUpdate Require Import RecordUpdate. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * MessageTuple 
    This file contains the wrapper around messages used
    by the network functionality.  
**)

Record MessageTuple :=
  mkMessageTuple
    { msg : Message
    ; rcv : Party
    ; cd : Delay }.

Instance MessageTupleSettable : Settable MessageTuple :=
  settable! mkMessageTuple <msg; rcv; cd>. 

Definition MessagePool := seq MessageTuple.

Module MessageTupleEq.

Definition eq_msg_tuple a b :=
  [&& msg a == msg b
   , rcv a == rcv b
   & cd a  == cd b ].

Lemma eq_msg_tupleP : Equality.axiom eq_msg_tuple.
Proof.
  case => ???; case => ???. rewrite /eq_msg_tuple /=.
  do ! (case: _ /eqP; [move => -> |by constructor; case]).
  by constructor.
Qed.


HB.instance Definition MessageTuple_eqMixin := hasDecEq.Build MessageTuple eq_msg_tupleP.

End MessageTupleEq.
Export MessageTupleEq.
