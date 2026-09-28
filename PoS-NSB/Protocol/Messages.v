From mathcomp Require Import
     all_ssreflect.
From HB Require Import
     structures.
From AUChain Require Import
     Parameters
     Blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Messages
      This file contains the basic message type used for communication. 
**)

Inductive Message :=
  | BlockMsg of Block.

Definition Messages := seq Message.

Module MsgEq.
Definition eq_msg a b :=
 match a, b with
 | BlockMsg bA, BlockMsg bB => (bA == bB)
  end.

Lemma eq_msgP : Equality.axiom eq_msg.
Proof. by move=> /= [] ? [] ? /=; apply/(iffP idP)=> [/eqP ->| [] -> ] //. Qed. 


HB.instance Definition _ := hasDecEq.Build Message eq_msgP.
End MsgEq.

Export MsgEq.
