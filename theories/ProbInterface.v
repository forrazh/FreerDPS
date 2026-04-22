From mathcomp Require Import reals.
From infotheo Require Import realType_ext.

From FreerDPS Require Import Init Interface Impure.

Generalizable All Variables.

Local Open Scope monae_scope.

Module Export ProbIfaceMod.
    Section prob_sec.
        Context {R : realType}.
Inductive prob_interface : interface :=
| CanWork (p : {prob R}) : prob_interface bool
.

Definition can_work  `{Provide ix prob_interface} {im : impureMonad ix} (p:{prob R}) : im bool := ( trigger  (inj_p $ CanWork p)).

Program Definition fail_track_op  `{Provide ix prob_interface} {im : impureMonad ix} 
    (p:{prob R}) `(k : im x) : im (option x) := can_work p >>= (fun ok => if ok then k >>= (fun a => Ret $ Some a) else Ret None).
    End prob_sec.
End ProbIfaceMod.
