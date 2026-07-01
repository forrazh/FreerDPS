From mathcomp Require Import ssreflect ssrbool seq.
From FreerDPS Require Import Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope nat_scope.

Generalizable All Variables.

Module StoreProduct.

Fixpoint product (l : seq nat) (p : nat) : nat :=
  match l with
  | [::] => p
  | n :: l' => product l' (n * p)
  end.

Fixpoint sproduct `{Provide ix (STORE nat)} {im : impureMonad ix}
    (l : seq nat) : im unit :=
  match l with
  | [::] => Ret tt
  | hd :: tl =>
      bind iget (fun p =>
        bind (iput (hd * p)) (fun _ => sproduct tl))
  end.

Definition final_store_value (sem : semantics (STORE nat)) : nat :=
  eval_effect sem Get.

Lemma sproduct_store_semantics (l : seq nat) p :
  final_store_value
    (exec_impure (store p)
      (sproduct (im:=ImpureModule_acto__canonical__Impure_MonadImpure (STORE nat)) l))
  = product l p.
Proof.
  move: p.
  elim: l => [|hd tl IH] p //=.
  exact: IH.
Qed.

Lemma sproduct_run_semantics (l : seq nat) p :
  run_impure (store p)
    (sproduct (im:=ImpureModule_acto__canonical__Impure_MonadImpure (STORE nat)) l)
  = (tt, store (product l p)).
Proof.
  move: p.
  elim: l => [|hd tl IH] p //=.
  exact: IH.
Qed.

End StoreProduct.
