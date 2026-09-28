From mathcomp Require Import
     all_ssreflect.

From AUChain Require Import
     Parameters.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Blocks
    This file contain the basic record representing a block. 
**)
Record Block :=
  MkBlock
    { sl : Slot
    ; txs : Transactions
    ; pred : Hash
    ; bid : Party }.

(* Type synononym for blocks *)
Definition Chain := seq Block.
Definition Chains := seq Chain.
Definition BlockPool := seq Block.

(* Decidable equality for Blocks *)
Definition eq_block (b b' : Block) :=
  match b, b' with
  | MkBlock sl txs pt bid, MkBlock sl' txs' pt' bid' =>
    [&& sl == sl', txs == txs', pt == pt' & bid == bid']
  end.

Lemma eq_blockP : Equality.axiom eq_block.
Proof.
  case => sl txs pt bid; case => sl'f txs' pt' bid' .
  rewrite /eq_block.
  do ! (case: _ /eqP; [move => -> |by constructor; case]).
  by constructor.
Qed.

HB.instance Definition _ :=  hasDecEq.Build Block eq_blockP.

(* Canonial structures for block *)

(** Parameters for block *)
Parameter GenesisBlock : Block.
Parameter HashB : Block -> Hash.
