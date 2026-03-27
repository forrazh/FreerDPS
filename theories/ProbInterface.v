Module ProbIfaceMod.
    Section prob_sec.
        Context {R : realType}.
Inductive prob_interface : interface :=
| CanWork (p : {prob R}) : prob_interface bool
.

Definition can_work  `{Provide ix prob_interface} {im : impureMonad ix} (p:{prob R}) : im bool := ( trigger  (inj_p $ CanWork p)).

    End prob_sec.
End ProbIfaceMod.