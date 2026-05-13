Ltac typeof X := type of X.

From Stdlib Require Import ssrmatching .
From mathcomp Require Import ssreflect ssrnum ssrbool ssralg  reals interval_inference. 
From infotheo Require Import realType_ext.

From HB Require Import structures.
From monae Require Import preamble hierarchy monad_lib proba_lib proba_model.


Local Open Scope monae_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.
Check choice.
(* 1st step : FlipMonad *)
HB.mixin Record isMonadFlip {R : realType} (M : UU0 -> UU0) of Monad M := {
    flip : forall (p : {prob R}), M bool ;
    (* identity axiom *)
    flip1 : flip 1%:i01 = Ret true  ;
    (* skewed commutativity *)
    flipNeg : forall (p: {prob R}), flip p = flip p%:num.~%:i01 >>= (fun x => Ret (~~x)) ;
    (* idempotence *)
    flipmm : forall (A:UU0) p (a:M A), flip p >> a = a ;
    (* quasi associativity *)
    (* flipA : forall (p q r s : {prob R}),
          flip p           >>= (fun a => flip q           >>= (fun b => Ret ))) 
        = flip [r_of p, q] >>= (fun a => flip [s_of p, q] >>= (fun b => Ret (a && b))) *)
    fA0:forall (T:UU0) (p q r s : {prob R}) (a b c : M T), 
    (* Prob.p p = (Prob.p r * Prob.p s)%R :> R -> ((Prob.p s).~ = (Prob.p p).~ * (Prob.p q).~)%R -> *)
flip p >>= (fun x => if x then a else flip q >>= (fun x0 => if x0 then b else c)) = 
flip [s_of p, q] >>= 
  (fun x => if x then flip [r_of p, q] >>= (fun x0 => if x0 then a else b) else c) ;   
}.

#[short(type=flipMonad)]
HB.structure Definition MonadFlip {R : realType} := {M of isMonadFlip R M & }.

Local Open Scope reals_ext_scope.

Module FlipLib.
  (* ===========  correct =========== *)
    Section proba2flipM.
        Variable R : realType.
        Variable M : probMonad R.

 		Let flip_c (p : {prob R}) : M bool := bcoin p.


(*** identity laws ***)
Let flip1 : flip_c 1%:i01 = Ret true.
Proof. exact: choice1. Qed.

(*** negation law ***)
Let flipNeg : forall p, flip_c p =  (flip_c (p%:num.~ %:i01)) >>= (fun x => Ret (~~ x)).
Proof.
  by move=>p; rewrite /flip_c/bcoin-choiceC choice_bindDl!bindretf.
Qed.

(*** skewed commutativity law ***)
Let flipmm : forall (A:UU0) (p:{prob R}) (a : M A), flip_c p >> a = a.
Proof.
  move=>A p a; rewrite/flip_c/bcoin choice_bindDl 2!bindretf.
  exact: choicemm.
Qed.

(*** quasi assoc law ***)
Let flipA : forall (T:UU0) (p q r s : {prob R}) (a b c : M T), 
	  flip_c p           >>= (fun x : bool => if x then a    else flip_c q >>= (fun x0 : bool => if x0 then b else c)) 
	= flip_c [s_of p, q] >>= (fun x : bool => if x then flip_c [r_of p, q] >>= (fun x0 : bool => if x0 then a else b) else c).
Proof.
  move=>T p q r s a b c.
  rewrite /flip_c/bcoin!choice_bindDl!bindretf.
  exact:choiceA.
Qed.
 
  #[non_forgetful_inheritance]
  HB.instance Definition t_ := isMonadFlip.Build R M flip1 flipNeg flipmm flipA.

	End proba2flipM.

	(* =========== complete =========== *)
	Section flip2probaM.
		Variable R : realType.
		Variable M : flipMonad R.

Let choicef (p : {prob R}) (A:UU0) (a b : M A) : M A := flip p >>= (fun x => if x then a else b). 



(*** identity laws ***)
Let choice1 : forall (A:UU0) (a b : M A), choicef 1%:i01 a b =  a.
Proof.
  move=>A a b/=. by rewrite /choicef flip1 bindretf.
Qed.  

(*** negation law ***)
Let choiceC : forall (A : UU0) (p:{prob R}) (a b : M A), choicef p a b = choicef (p%:num.~ %:i01) b a.
Proof.
  move=> A p a b.
  rewrite /choicef flipNeg bindA. 
  congr (flip _ >>= _).
  by apply/boolp.funext=>x;
    rewrite bindretf if_neg.
Qed.


(*** skewed commutativity law ***)
Let choicemm : forall (A : UU0) (p : {prob R}) (a : M A), choicef p a a = a.
Proof.
  move=>A p a.
  rewrite /choicef -{3}(flipmm A p a).
  congr (flip p >> _).
  apply/boolp.funext=>x;
    exact/if_same.
Qed.

(*** quasi assoc law ***)
Let choiceA :
        forall (T : UU0) (p q : {prob R}),
        forall a b c : M T,
        choicef p a (choicef q b c) =
        choicef [s_of p, q] (choicef [r_of p, q] a b) c.
Proof.
  by rewrite/choicef=>A p q a b c; apply: fA0. 
Qed.

Set Warnings "-redundant-canonical-projection".

		#[non_forgetful_inheritance]
    HB.instance Definition _ := isMonadConvex.Build R M choicef choice1 choiceC choicemm choiceA.

Let prob_bindDl p :
  BindLaws.left_distributive ( @hierarchy.bind M) (fun A => @choicef p A).
Proof.
move=> A B m1 m2 k.
rewrite !/choicef bindA. 
congr (flip p >>= _).
by apply/boolp.funext; case.
Qed.

 #[non_forgetful_inheritance]
HB.instance Definition _ := isMonadProb.Build R M prob_bindDl.

	End flip2probaM.
End FlipLib.

HB.export FlipLib.

Module FlipModel.
  (* === test with ret/bind === *)
Section ConcreteFlip.
  Variable R : realType.

  Definition flipacto := MonadProbModel.acto R.


Notation pr := (probMonad R).

Definition cflip (p : {prob R}) := @bcoin R flipacto p.

(*** identity laws ***)
Let flip1 : @cflip 1%:i01 = ret R bool true.
Proof. exact: choice1. Qed.

Ltac rw_choicebind_dl:=rewrite /cflip choice_bindDl!bindretf/=.

(*** negation law ***)
Let flipNeg : forall p, cflip p = (cflip (p%:num.~ %:i01) >>= (fun x => ret R bool (~~ x))).
Proof. 
  move=>p. 
  rw_choicebind_dl;
    exact: choiceC.
Qed.


(*** skewed commutativity law ***)
Let flipmm : forall (A:UU0) (p:{prob R}) (a : flipacto A), (cflip p >>= (fun _ => a)) = a.
Proof. 
  move=>A p a.
  rw_choicebind_dl; exact:choicemm.
Qed.

(*** quasi assoc law ***)
Let flipA : forall (T:UU0) (p q r s : {prob R}) (a b c : flipacto T), 
	  (cflip p           >>= (fun x : bool => if x then a   else (cflip q >>= (fun x0 : bool => if x0 then        b  else c))))
	= (cflip [s_of p, q] >>= (fun x : bool => if x then cflip [r_of p, q] >>= (fun x0 : bool => if x0 then a else b) else c  )).
Proof.
  move=>T p q r s a b c.
  repeat rw_choicebind_dl. exact: choiceA.
Qed. 

    HB.instance Definition _ := Monad.on flipacto.
		HB.instance Definition _ := isMonadFlip.Build R flipacto flip1 flipNeg flipmm flipA.

End ConcreteFlip.
End FlipModel. 