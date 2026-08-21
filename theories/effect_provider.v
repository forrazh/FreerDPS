From mathcomp Require Import ssreflect ssrfun seq.
From monae Require Import hierarchy.
From FreerDPS Require Import init effect.

Check effect.

(* We want a generic StrictProvide that have such a type signature *)
(* It should be able to Provide all effects in Fs in Fx. *)
(* It should also Distinguish all effects present in Fs. *)
Class StrictProvide (Fx : effect) (Fs : seq effect) : Type := {}.

(* While testing that everything works with the strict provide, this module will be added there *)
Module StrictProvideTests.

Section TwoEffects.
Variables Fx F G : effect.
Context `{[:: F; G] -<< Fx}.

Goal Distinguish Fx F G.
Proof. exact: _. Qed.

Goal Distinguish Fx G F.
Proof. exact: _. Qed.
End TwoEffects.

Section ThreeEffects.
Variables Fx F G H : effect.
Context `{[:: F; G; H] -<< Fx}.

Goal H -< Fx.
Proof. exact: _. Qed.

Goal Distinguish Fx F G.
Proof. exact: _. Qed.

Goal Distinguish Fx G F.
Proof. exact: _. Qed.

Goal Distinguish Fx F H.
Proof. exact: _. Qed.

Goal Distinguish Fx H F.
Proof. exact: _. Qed.

Goal Distinguish Fx G H.
Proof. exact: _. Qed.

Goal Distinguish Fx H G.
Proof. exact: _. Qed.
End ThreeEffects.

Section FourEffects.
Variables Fx F G H I : effect.
Context `{[:: F; G; H; I] -<< Fx}.

Goal I -< Fx.
Proof. exact: _. Qed.

Goal Distinguish Fx F G.
Proof. exact: _. Qed.

Goal Distinguish Fx G F.
Proof. exact: _. Qed.

Goal Distinguish Fx F H.
Proof. exact: _. Qed.

Goal Distinguish Fx H F.
Proof. exact: _. Qed.

Goal Distinguish Fx F I.
Proof. exact: _. Qed.

Goal Distinguish Fx I F.
Proof. exact: _. Qed.

Goal Distinguish Fx G H.
Proof. exact: _. Qed.

Goal Distinguish Fx H G.
Proof. exact: _. Qed.

Goal Distinguish Fx G I.
Proof. exact: _. Qed.

Goal Distinguish Fx I G.
Proof. exact: _. Qed.

Goal Distinguish Fx H I.
Proof. exact: _. Qed.

Goal Distinguish Fx I H.
Proof. exact: _. Qed.
End FourEffects.

End StrictProvideTests.
