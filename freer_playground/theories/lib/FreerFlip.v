From Stdlib Require Import ssrmatching Reals JMeq Relations Morphisms Eqdep.
From mathcomp Require Import ssreflect ssrbool ssrnum ssralg reals interval_inference. 
From infotheo Require Import realType_ext.
From HB Require Import structures.
From monae Require Import preamble hierarchy monad_lib.
From FreerTheories Require Import FlipMonad FreerMonad.

Declare Scope freer_flip_scope.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope freer_flip_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.

Reserved Notation "x <|| p ||> y" (at level 40, left associativity, y at next level).
Reserved Notation "a === b" (at level 90).

Module FreerFlipModel.

  Section freer_flip.
Variable R:realType.
		 
Inductive FlipEff : UU0 -> UU0 :=
| flip_e (p : {prob R}) : FlipEff bool
.


Arguments trigger {_ _ _}.
Variable M : (freerMonad FlipEff).


Definition flipf (p:{prob R}) := ( @trigger FlipEff M bool (flip_e p)).


(* Let fa := flipacto R. *)
Variable fl : flipMonad R.

Definition denote_flip_effect : FlipEff ~~> fl := 
fun X fx => match fx with 
| flip_e p => flip p
end.

Notation choice_of_Type := monad_model.choice_of_Type.

Definition choicef {X} (p : {prob R}) (a b : M X) := flipf p >>= (fun b0 => if b0 then a else b).

Notation "x <|| p ||> y" := 
  (choicef p x y) 
(at level 40, left associativity, y at next level) : freer_flip_scope.


(* 5th step : Flip equiv laws *)
Inductive flip_rel :forall `[X : UU0] (m1 m2 : M X), Prop := 
| rflip1 : flip_rel (flipf 1%:i01) (Ret true)
| rflipNeg : forall p, flip_rel (flipf p) ((flipf p%:num.~%:i01) >>= (fun x => Ret (~~ x)))
| rflipmm : forall (A:UU0) p (a: (M A)), flip_rel (flipf p >> a) a 
    (* quasi associativity *)
| rflipA : forall (T:UU0) (p q r s : {prob R}) (a b c : M T),  flip_rel
    (a <|| p ||> (b <|| q ||> c)) 
    ((a <|| [r_of p, q] ||> b) <|| [s_of p, q] ||> c)
  (* (flipf p >>= (fun x : bool => if x then a else flipf q >>= (fun x0 : bool => if x0 then b else c))) *)
  (* (flipf [s_of p, q] >>= (fun x : bool => if x then flipf [r_of p, q] >>= (fun x0 : bool => if x0 then a else b) else c))  *)
| equiv_bind_congr : forall (A B :UU0) (a b : M A) (f g : A -> M B), 
  (* a === b -> (forall x, (f x) === (g x)) -> (a >>= f) === (b >>= g) *)
  flip_rel a b -> (forall x, flip_rel (f x) (g x)) -> flip_rel (a >>= f) (b >>= g)
| equiv_refl : forall (A:UU0) (m : M A), flip_rel m m
| equiv_sym : forall (A:UU0) (m n : M A), flip_rel m n -> flip_rel n m
| equiv_trans : forall (A:UU0) (m n o : M A), flip_rel m n -> flip_rel n o -> flip_rel m o
.

(* 6th step : Equiv correct *)
Lemma equiv_correct : forall (X : UU0) (m1 m2 : M X),
     @flip_rel X m1 m2 ->
      denote fl denote_flip_effect X m1 = denote fl denote_flip_effect X m2.
Proof.
  move=>X m1 m2 H.
  (* rewrite/denote/=.  *)
  elim: H=>[| p | A p a | T p q r s a b c 
  | A B a b f g Hab H Hfg H'
  | A m | A m n Hmn H | A m n o Hmn H Hno H'
  ]/=
  ; last first.
  - by rewrite H H'.
  - by rewrite H.
  - by [].
  - rewrite !denote_bind ; congr bind.
    + exact/H.
    + apply/boolp.funext/H'.
  (* all: rewrite/=. *)
  all: rewrite ?denote_bind.
  (* flip_a  *)
    under eq_bind do rewrite denote_if denote_bind;
    under [in RHS]eq_bind do rewrite denote_if denote_bind;
    under eq_bind do under eq_bind do rewrite denote_if;
    under [in RHS]eq_bind do under eq_bind do rewrite denote_if.
  all: rewrite !denote_trigger/denote_flip_effect.
  - exact/fA0. 
  - exact/flipmm.
  - under eq_bind do rewrite denote_ret. exact/flipNeg.
  - rewrite denote_ret; exact/flip1.
Qed.

HB.instance Definition _ := isFreerEquiv.Build FlipEff equiv_correct.

Notation "a === b" :=
(flip_rel a b)
  (at level 90) : freer_flip_scope.

End freer_flip.
End FreerFlipModel.

HB.export FreerFlipModel.

Arguments flip_rel {_ _ _}.
Arguments flipf {_ _}.
Arguments choicef {_ _ _}.



