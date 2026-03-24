
(* ======== Freeeeeee ======== *)

(* Check monadM.

HB.mixin Record isFreerMonadCoproduct (F G : Eff) (mf : freerMonad F) (mg : freerMonad G) (cm : monad) (M : UU0 -> UU0) of freerMonad (F<+>G) M := {
    cp_left  : monadM (mf) M ;
    cp_right : monadM mg M ;
    from_coproduct : (mf ~~> cm) -> (mg ~~> cm) -> (M ~~> cm) ; 
    cp_left_law  : forall (f : monadM mf cm) (g : monadM mg cm) X (m : mf X),  from_coproduct f g X (cp_left X m)  = f X m ;
    cp_right_law : forall (f : monadM mf cm) (g : monadM mg cm) X (m : mg X), from_coproduct f g X (cp_right X m) = g X m ;
    from_coproduct_unique : forall (f : monadM mf cm) (g : monadM mg cm) (c : monadM M cm), (forall X m, c X (cp_left X m) = from_coproduct f g X (cp_left X m)) -> (forall X m, c X (cp_right X m) = from_coproduct f g X (cp_right X m)) -> forall X m, from_coproduct f g X m = c X m
}.

#[short(type=coprodMF)]
HB.structure Definition CoproductOfMonads (freerMonad F freerMonad G cm : monad) := {M of isMonadCoproduct freerMonad F freerMonad G cm M &}. 


Module FLeftCoprod.
    Section leftc.
        Variable F G : UU0 -> UU0.
        Variable Mf : freerMonad F.
        Variable Mfg : freerMonad (F <+> G).
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
