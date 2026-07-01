From mathcomp Require Import ssreflect ssrbool ssrnum ssralg reals interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import monad_lib proba_lib.

From FreerDPS Require Import Init Interface Impure Component.

Generalizable All Variables.

Module Export ProbIfaceMod.
    Section prob_sec.
        Context {R : realType}.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Inductive prob_interface : interface :=
| CanWork (p : {prob R}) : prob_interface bool
.

Definition can_work  `{Provide ix prob_interface} {im : impureMonad ix} (p:{prob R}) : im bool := ( trigger  (inj_p $ CanWork p)).

Definition prob_flip `{Provide ix prob_interface} {im : impureMonad ix}
    (p : {prob R}) : im bool :=
  can_work p.

Definition prob_choice `{Provide ix prob_interface} {im : impureMonad ix}
    {X} (p : {prob R}) (a b : im X) : im X :=
  bind (prob_flip p) (fun ok => if ok then a else b).

Program Definition fail_track_op  `{Provide ix prob_interface} {im : impureMonad ix} 
    (p:{prob R}) `(k : im x) : im (option x) :=
  bind (can_work p)
    (fun ok =>
       if ok then bind k (fun a => Ret $ Some a)
       else Ret None).

Inductive probify_interface (i : interface) : interface :=
| ProbCall : forall X, {prob R} -> i X -> probify_interface i (option X).

Arguments ProbCall [i X] _ _.

Definition prob_call `{Provide ix (probify_interface i)} {im : impureMonad ix}
    {X} (p : {prob R}) (e : i X) : im (option X) :=
  trigger (inj_p $ ProbCall p e).

Fixpoint lift_impure {i ix X} `{Provide ix i} (p : impure i X) : impure ix X :=
  match p with
  | local x => local x
  | request_then _ e k =>
      request_then (inj_p e) (fun x => lift_impure (k x))
  end.

Definition prob_component {i j : interface}
    (c : component (im:=Impure.ImpureModule_acto__canonical__Impure_MonadImpure j) i j)
  : component
      (im:=Impure.ImpureModule_acto__canonical__Impure_MonadImpure (j + prob_interface))
      (probify_interface i) (j + prob_interface) :=
  fun X e =>
    match e in probify_interface _ Y return impure (j + prob_interface) Y with
    | @ProbCall _ _ p op =>
        fail_track_op
          (im:=Impure.ImpureModule_acto__canonical__Impure_MonadImpure (j + prob_interface))
          p (lift_impure (ix:=j + prob_interface) (c _ op))
    end.

Definition iprob_flip {ix} `{Provide ix prob_interface}
    (p : {prob R}) : impure ix bool :=
  prob_flip (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) p.

Definition iprob_choice {ix} `{Provide ix prob_interface}
    {X} (p : {prob R}) (a b : impure ix X) : impure ix X :=
  prob_choice (im:=ImpureModule_acto__canonical__Impure_MonadImpure ix) p a b.

Inductive prob_rel {ix} `{Provide ix prob_interface} {im : impureMonad ix}
    : forall X, im X -> im X -> Prop :=
| rprob1 :
    prob_rel _ (prob_flip (im:=im) (1%:i01)) (Ret true)
| rprobNeg p :
    prob_rel _ (prob_flip (im:=im) p)
      (bind (prob_flip (im:=im) (p%:num.~%:i01))
        (fun x => Ret (~~ x)))
| rprobmm A p (a : im A) :
    prob_rel _ (bind (prob_flip (im:=im) p) (fun _ => a)) a
| rprobA T (p q r s : {prob R}) (a b c : im T) :
    prob_rel _
      (prob_choice (im:=im) p a (prob_choice (im:=im) q b c))
      (prob_choice (im:=im) [s_of p, q]
        (prob_choice (im:=im) [r_of p, q] a b) c)
| prob_rel_bind_congr A B (a b : im A) (f g : A -> im B) :
    prob_rel _ a b ->
    (forall x, prob_rel _ (f x) (g x)) ->
    prob_rel _ (bind a f) (bind b g)
| prob_rel_refl A (m : im A) :
    prob_rel _ m m
| prob_rel_sym A (m n : im A) :
    prob_rel _ m n -> prob_rel _ n m
| prob_rel_trans A (m n o : im A) :
    prob_rel _ m n -> prob_rel _ n o -> prob_rel _ m o.

    End prob_sec.
End ProbIfaceMod.
