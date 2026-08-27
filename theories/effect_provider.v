From mathcomp Require Import ssreflect ssrfun seq.
From monae Require Import hierarchy.
From FreerDPS Require Import init effect.

(** Code excerpt from Section 5.2 of:
    A. Saito and R. Affeldt, "Experimenting with an Intrinsically-typed
    Probabilistic Programming Language in Coq", APLAS 2023.
    https://staff.aist.go.jp/reynald.affeldt/documents/syntax-aplas2023.pdf
  *)
Section tagged_context.
Let ctx := seq (effect).
Implicit Types (eff : effect) (g : ctx) (X: UU0).

(* Definition dom g := map fst g. *)

Inductive EMember (F: effect) : seq effect -> Type :=
| EM0 Fs : EMember F (F :: Fs)
| EMNext G Fs :
    EMember F Fs -> EMember F (G :: Fs).

Arguments EM0 {F Fs}.
Arguments EMNext {F G Fs} EMemberF.

Definition lookup g eff := EMember eff g.
Check EMember _.
(* nth t0 (map snd g) (index F (dom g)). *)

Structure tagged_ctx := Tag {untag : ctx}.

Structure find eff := Find {
  ctx_of : tagged_ctx ;
  #[canonical=no] ctx_prf : lookup (untag ctx_of) eff}.

Lemma ctx_prf_head eff g : lookup (eff :: g) eff.
Proof. constructor. Qed.

Lemma ctx_prf_tail F g F' :
  lookup g F ->
  lookup (F' :: g) F.
Proof.
rewrite /lookup.
elim=>[Fs| G Fs hprev ih] /=.
- exact/EMNext/EM0.
- exact/EMNext/EMNext.
Qed.

Definition recurse_tag g := Tag g.
Canonical found_tag g := recurse_tag g.

Canonical found F g : find F :=
  @Find F (found_tag (F :: g))
              (@ctx_prf_head F g).


Check ctx_prf.
Canonical recurse eff eff' (g : find eff) : find eff :=
  Find eff (recurse_tag (eff' :: untag (ctx_of eff g))) (ctx_prf_tail eff (untag (ctx_of eff g)) eff' (ctx_prf eff g)).

End tagged_context.
Check effect.

(* We want a generic CanSp that have such a type signature *)
(* It should be able to Provide all effects in Fs in Fx. *)
(* It should also Distinguish all effects present in Fs. *)
Class CanSp (Fx : effect) (Fs : seq effect) : Type := {}.
Notation "Fs -<< Fx" := (CanSp Fx Fs)
  (at level 50, no associativity) : type_scope.

(* While testing that everything works with the strict provide, this module will be added there *)
Module CanSpTests.

Section TwoEffects.
Variables Fx F G : effect.
Context `{[:: F; G] -<< Fx}.

Goal F -< Fx.
Proof. exact: _. Qed.

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

End CanSpTests.
