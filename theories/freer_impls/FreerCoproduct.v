
Require Import ssrmatching Reals JMeq.
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct. *)
(* From infotheo Require Import realType_ext ssr_ext fsdist convex. *)
From HB Require Import structures.
From monae Require Import preamble hierarchy.
(* From monae Require Import monad_lib. *)
Print LoadPath.
From FreerDPS Require Import FreerMonad.

Local Open Scope monae_scope.
Local Close Scope nat_scope.
Declare Scope fm_scope.
Local Open Scope fm_scope.

(* Step 3 *)
Notation "F <+> G" := (fun X:Type => F X + G X)%type (at level 50) : fm_scope.
 
Check monadM.

HB.mixin Record isMonadCoproduct (N N': monad) (M : UU0 -> UU0) of Monad M := {
    cp_left  : monadM N M ;
    cp_right : monadM N' M ;
    from_coproduct : forall (cm : monad), 
    (N ~~> cm) -> (N' ~~> cm) -> (M ~~> cm) ; 
    cp_left_law  : 
        forall cm 
        (f : monadM N cm) 
        (g : monadM N' cm) 
        X 
        (m : N X),  
        from_coproduct cm f g X (cp_left X m)  = f X m ;
    cp_right_law : forall (cm : monad) (f : monadM N cm) (g : monadM N' cm) X (m : N' X), 
        from_coproduct cm f g X (cp_right X m) = g X m ;
    from_coproduct_unique : forall (cm : monad) (f : monadM N cm) (g : monadM N' cm) (c : monadM M cm), 
        (forall X m, c X (cp_left X m) = from_coproduct cm f g X (cp_left X m)) 
        -> (forall X m, c X (cp_right X m) = from_coproduct cm f g X (cp_right X m)) 
        -> forall X m, from_coproduct cm f g X m = c X m
}.

#[short(type=coprodM)]
HB.structure Definition CoproductOfMonads (N N' : monad) := {M of isMonadCoproduct N N' M &}.


Module LeftCoprod.
    Section leftc.
        Variable F G : UU0 -> UU0.

Fixpoint mmor_left [X] (mf : acto F X) : acto (F <+> G) X := match mf with 
| Pure x => Pure (F <+> G) x
| Impure Y fy k => Impure (inl fy) (fun y => mmor_left (k y))
end. 

Let ret : MonadMLaws.ret mmor_left.
Proof.
    by [].
Qed.

Let bind : MonadMLaws.bind mmor_left.
Proof.
    move=>a b m f.
    elim: m=>[x|Y fy k H]//=.
    congr (Impure);
    apply/boolp.funext=>y.
    by rewrite H.
Qed.

(* HB.about isMonadM_ret_bind.Build. *)
HB.instance Definition _ := isMonadM_ret_bind.Build (acto F) (acto (F<+>G)) mmor_left ret bind.

    End leftc.
End LeftCoprod.
HB.export LeftCoprod.

Module RightCoprod.
    Section righc.
        Variable F G : UU0 -> UU0.

Fixpoint mmor_right [X] (mf : acto G X) : acto (F <+> G) X := match mf with 
| Pure x => Pure (F <+> G) x
| Impure Y fy k => Impure (inr fy) (fun y => mmor_right (k y))
end. 

Let ret : MonadMLaws.ret mmor_right.
Proof.
    move=>a.
    by [].
Qed.

Let bind : MonadMLaws.bind mmor_right.
Proof.
    move=>a b m f.
    elim: m=>[x|Y fy k H]//=.
    congr (Impure);
    apply/boolp.funext=>y.
    by rewrite H.
Qed.

(* HB.about isMonadM_ret_bind.Build. *)
HB.instance Definition _ := isMonadM_ret_bind.Build (acto G) (acto (F<+>G)) mmor_right ret bind.

    End righc.
End RightCoprod.
HB.export RightCoprod.

Module FullCoprod.
    Section cop.
    Variable F G : UU0 -> UU0.
    Check acto.
    Notation Nacto := (acto F).
    Notation Nacto':= (acto G).
    Notation Macto := (acto (F<+>G)).
    (* Variable cm : monad. *)
    (* Variable (l : Nacto ~~> cm). *)
    (* Variable X Y:UU0. *)
    (* Varible *)

Variable ammor_left : forall {X} (MF:mathFreerMonad F) (MFG:mathFreerMonad (F <+> G)) (mf : MF X), MFG X.
Variable ammor_right : forall {X} (MG:mathFreerMonad G) (MFG:mathFreerMonad (F <+> G)) (mg : MG X), MFG X.
    (* Check (l X (@Impure F X Y (F Y) (fun y => @Pure F y))). *)
Definition ctrigger `{X:UU0} (MF:mathFreerMonad F) (MG:mathFreerMonad G) {MFG : mathFreerMonad (F<+>G)} (fg : (F<+>G) X) 
    : MFG X. 
Proof.
    case: fg=>[fx|gx].
    apply/(ammor_left MF)/trigger/fx.
    apply/(ammor_right MG)/trigger/gx.
Defined.     
Print ctrigger.

Definition easytrigger : (F<+>G) ~~> Macto := fun X fg =>
Impure fg (fun x => Pure (F<+>G) x).
(* move=>X fg. apply/Impure. apply/fg. apply/Pure.
Show Proof.
:= fun fgy => match fgy with
| inl f => (Impure f (fun y => Pure (F<+>G) y))
| inr g => (Impure g (fun y => Pure (F<+>G) y))
end
. *)

Goal forall X fg, @ctrigger X Nacto Nacto' Macto  fg = easytrigger X fg.
move=>X; case=>[fx|gx]/=.
    Local Fixpoint from_coproduct (cm : monad) (l : Nacto ~~> cm) (r : Nacto' ~~> cm) `[X:UU0] (m : Macto X) : cm X
:= match m with 
| Pure x => ret X x 
| Impure Y fgy k => match fgy with
    | inl f => l Y (Impure f (fun y:Y => Pure F y))
    | inr g => r Y (Impure g (fun y:Y => Pure G y))
    end >>= fun y => from_coproduct cm l r (k y)
end
.

Notation mmor_l := (mmor_left F G).
Notation mmor_r := (mmor_right F G).


Let cp_left_law  : forall (cm : monad) (f : monadM Nacto cm) (g : monadM Nacto' cm) X (m : Nacto X), from_coproduct cm f g (mmor_l m) = f X m.
Proof.
    move=>cm f g X.
    elim=>[x|Y fy k H]/=.
        by rewrite -(monadMret (s:=f)).
    under eq_bind do rewrite H.
    by rewrite -monadMbind.
Qed.
Let cp_right_law  : forall (cm : monad) (f : monadM Nacto cm) (g : monadM Nacto' cm) X (m : Nacto' X),  from_coproduct cm f g (mmor_r m)  = g X m.
Proof.
    move=>cm f g X.
    elim=>[x|Y fy k H]/=.
        by rewrite -(monadMret (s:=g)).
    under eq_bind do rewrite H.
    by rewrite -monadMbind.
Qed.

Let from_coproduct_unique : forall (cm : monad) (f : monadM Nacto cm) (g : monadM Nacto' cm) (c : monadM Macto cm), (forall X m, c X (mmor_l m) = from_coproduct cm f g (mmor_l m)) -> (forall X m, c X (mmor_r m) = from_coproduct cm f g (mmor_r m)) -> forall X m, from_coproduct cm f g m = c X m.
Proof.
    move=>cm f g c Hl Hr X.
    elim=>[x|Y fgy ky H]/=.
    by rewrite/=-(monadMret (s:=c)).
    under eq_bind do rewrite H.
    by case: fgy=>[fy|gy]; 
        rewrite -?(cp_left_law  cm f g) -?Hl 
                -?(cp_right_law cm f g) -?Hr
            /=-(monadMbind (s:=c)).
     
Qed.

HB.about isMonadCoproduct.Build.
HB.instance Definition _ := isMonadCoproduct.Build (Nacto) (Nacto') (Macto) mmor_l mmor_r from_coproduct cp_left_law cp_right_law from_coproduct_unique.

    End cop.
End FullCoprod.

HB.export FullCoprod.

(* ======== Freeeeeee ======== *)

(* Check monadM.

HB.mixin Record isFreerMonadCoproduct (F G : Eff) (mf : mathFreerMonad F) (mg : mathFreerMonad G) (cm : monad) (M : UU0 -> UU0) of MathFreerMonad (F<+>G) M := {
    cp_left  : monadM (mf) M ;
    cp_right : monadM mg M ;
    from_coproduct : (mf ~~> cm) -> (mg ~~> cm) -> (M ~~> cm) ; 
    cp_left_law  : forall (f : monadM mf cm) (g : monadM mg cm) X (m : mf X),  from_coproduct f g X (cp_left X m)  = f X m ;
    cp_right_law : forall (f : monadM mf cm) (g : monadM mg cm) X (m : mg X), from_coproduct f g X (cp_right X m) = g X m ;
    from_coproduct_unique : forall (f : monadM mf cm) (g : monadM mg cm) (c : monadM M cm), (forall X m, c X (cp_left X m) = from_coproduct f g X (cp_left X m)) -> (forall X m, c X (cp_right X m) = from_coproduct f g X (cp_right X m)) -> forall X m, from_coproduct f g X m = c X m
}.

#[short(type=coprodMF)]
HB.structure Definition CoproductOfMonads (mathFreerMonad F mathFreerMonad G cm : monad) := {M of isMonadCoproduct mathFreerMonad F mathFreerMonad G cm M &}. 


Module FLeftCoprod.
    Section leftc.
        Variable F G : UU0 -> UU0.
        Variable Mf : mathFreerMonad F.
        Variable Mfg : mathFreerMonad (F <+> G).
Definition mmor_left [X] (mf :  Mf X) : Mfg X.
case: mf.

:= match mf with 
| Pure x => Pure (F <+> G) x
| Impure Y fy k => Impure (inl fy) (fun y => mmor_left (k y))
end. 

Let ret : MonadMLaws.ret mmor_left.
Proof.
    by [].
Qed.

Let bind : MonadMLaws.bind mmor_left.
Proof.
    move=>a b m f.
    elim: m=>[x|Y fy k H]//=.
    congr (Impure);
    apply/boolp.funext=>y.
    by rewrite H.
Qed.

(* HB.about isMonadM_ret_bind.Build. *)
HB.instance Definition _ := isMonadM_ret_bind.Build (acto F) (acto (F<+>G)) mmor_left ret bind.
    End leftc.
End LeftCoprod.



 *)
