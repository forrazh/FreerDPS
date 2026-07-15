From mathcomp Require Import all_boot boolp interval_inference reals ssrnum ssralg.
From infotheo Require Import realType_ext.
From HB Require Import structures.
From monae Require Import preamble hierarchy monad_lib proba_lib.
From FreerDPS Require Import Impure.

Import FreerFuns.
Generalizable All Variables.

Declare Scope freer_flip_scope.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope freer_flip_scope.
Local Open Scope ring_scope.

Reserved Notation "x <|| p ||> y" (at level 40, left associativity, y at next level).
Reserved Notation "a === b" (at level 70).

Check trigger.

Module FreerFlipModel.

  Section freer_flip.
Variable R:realType.

Inductive FlipEff : UU0 -> UU0 :=
| flip_e (p : {prob R}) : FlipEff bool
.

Variable M : (freerMonad FlipEff).


Definition flipf  `{Provide ix FlipEff} {im : freerMonad ix} (p:{prob R}) : im bool := (trigger $ flip_e p).

Variable fl : probMonad R.

Definition denote_flip_effect : FlipEff ~~> fl :=
fun X fx => match fx with
| flip_e p => bcoin p
end.

Lemma denote_flip_effect_inj_pE (p : {prob R}) :
    denote_flip_effect bool (inj_p (flip_e p)) = bcoin p.
Proof.
  by [].
Qed.

Lemma denote_flipfE (p : {prob R}) :
    denote (s := M) fl denote_flip_effect bool (flipf p) = bcoin p.
Proof.
  by rewrite /flipf denote_request /denote_flip_effect.
Qed.

Definition choicef {X} (p : {prob R}) (a b : M X) := flipf p >>= (fun b0 => if b0 then a else b).

Lemma denote_choicefE (X : UU0) (p : {prob R}) (a b : M X) :
    denote (s := M) fl denote_flip_effect X (choicef p a b) =
      denote (s := M) fl denote_flip_effect bool (flipf p) >>=
        (fun b0 =>
          if b0 then denote (s := M) fl denote_flip_effect X a
          else denote (s := M) fl denote_flip_effect X b).
Proof.
  rewrite /choicef denote_bind /ssrfun.comp.
  under eq_bind do rewrite denote_if.
  by [].
Qed.

Notation "x <|| p ||> y" :=
  (choicef p x y)
(at level 40, left associativity, y at next level) : freer_flip_scope.

Lemma denote_choiceA_leftE (T : UU0) (p q : {prob R}) (a b c : M T) :
    denote (s := M) fl denote_flip_effect bool (flipf p) >>=
      ssrfun.comp (denote (s := M) fl denote_flip_effect T)
        (fun b0 => if b0 then a else b <|| q ||> c) =
    denote (s := M) fl denote_flip_effect bool (flipf p) >>=
      (fun b0 =>
        if b0 then denote (s := M) fl denote_flip_effect T a
        else denote (s := M) fl denote_flip_effect bool (flipf q) >>=
          (fun b1 =>
            if b1 then denote (s := M) fl denote_flip_effect T b
            else denote (s := M) fl denote_flip_effect T c)).
Proof.
  rewrite /ssrfun.comp.
  under eq_bind do rewrite denote_if denote_choicefE.
  by [].
Qed.

Lemma denote_choiceA_rightE (T : UU0) (p q : {prob R}) (a b c : M T) :
    denote (s := M) fl denote_flip_effect bool (flipf [s_of p, q]) >>=
      ssrfun.comp (denote (s := M) fl denote_flip_effect T)
        (fun b0 => if b0 then a <|| [r_of p, q] ||> b else c) =
    denote (s := M) fl denote_flip_effect bool (flipf [s_of p, q]) >>=
      (fun b0 =>
        if b0 then
          denote (s := M) fl denote_flip_effect bool
            (flipf [r_of p, q]) >>=
          (fun b1 =>
            if b1 then denote (s := M) fl denote_flip_effect T a
            else denote (s := M) fl denote_flip_effect T b)
        else denote (s := M) fl denote_flip_effect T c).
Proof.
  rewrite /ssrfun.comp.
  under eq_bind do rewrite denote_if denote_choicefE.
  by [].
Qed.


(* 5th step : Choice equiv laws *)
Inductive choice_rel :forall `[X : UU0] (m1 m2 : M X), Prop :=
| rchoice1 : forall (A : UU0) (a b : M A),
    choice_rel (choicef 1%:i01 a b) a
| rchoiceC : forall (A : UU0) (p : {prob R}) (a b : M A),
    choice_rel (choicef p a b) (choicef p%:num.~%:i01 b a)
| rchoicemm : forall (A : UU0) (p : {prob R}) (a : M A),
    choice_rel (choicef p a a) a
    (* quasi associativity *)
| rchoiceA : forall (T:UU0) (p q r s : {prob R}) (a b c : M T),  choice_rel
    (a <|| p ||> (b <|| q ||> c))
    ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c)
  (* (flipf p >>= (fun x : bool => if x then a else flipf q >>= (fun x0 : bool => if x0 then b else c))) *)
  (* (flipf [s_of p, q] >>= (fun x : bool => if x then flipf [r_of p, q] >>= (fun x0 : bool => if x0 then a else b) else c))  *)
| equiv_bind_congr : forall (A B :UU0) (a b : M A) (f g : A -> M B),
  (* a === b -> (forall x, (f x) === (g x)) -> (a >>= f) === (b >>= g) *)
  choice_rel a b -> (forall x, choice_rel (f x) (g x)) -> choice_rel (a >>= f) (b >>= g)
| equiv_refl : forall (A:UU0) (m : M A), choice_rel m m
| equiv_sym : forall (A:UU0) (m n : M A), choice_rel m n -> choice_rel n m
| equiv_trans : forall (A:UU0) (m n o : M A), choice_rel m n -> choice_rel n o -> choice_rel m o
.
(* 6th step : Equiv correct *)
Lemma equiv_correct : forall (X : UU0) (m1 m2 : M X),
     @choice_rel X m1 m2 ->
      denote fl denote_flip_effect X m1 = denote fl denote_flip_effect X m2.
Proof.
  move=>X m1 m2 H.
  (* rewrite/denote/=.  *)
  elim: H=> [*|*|*|*|*|*|????->|?????->?->] //=; last first; rewrite ?denote_bind.
  - by congr bind; [| apply/boolp.funext].

  rewrite denote_choiceA_leftE denote_choiceA_rightE.

  all: rewrite ?denote_request/ssrfun.comp!denote_flip_effect_inj_pE /bcoin !choice_bindDl !bindretf.
  - exact: choiceA.
  - exact: choicemm.
  - exact: choiceC.
  - exact: choice1.
Qed.

End freer_flip.
End FreerFlipModel.
