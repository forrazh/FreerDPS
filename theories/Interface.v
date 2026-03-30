From FreerDPS Require Export Init.
From HB Require Import structures.
From mathcomp Require Import ssrfun ssrbool.

Definition interface : UU0 := UU0 -> UU0.

Inductive iempty : interface := .

Inductive STORE (S : UU0) : interface := 
| Get : STORE S S 
| Put (s : S) : STORE S unit.

Arguments Get {S}.
Arguments Put [S] (s).


Module Feather.

    (* We need a hierarchy with a few structure, here we Equality -> Singleton *)
HB.mixin Record HasEqDec T := {
    eqtest : T -> T -> bool;
    eqOK : forall x y, reflect (x = y) (eqtest x y);
}.
HB.structure Definition Equality := { T of HasEqDec T }.

HB.mixin Record IsContractible T & HasEqDec T := {
    def : T;
    all_def : forall x, eqtest x def = true;
}.
HB.structure Definition Singleton := { T of IsContractible T }.

(*
   This is the type which is used as a feather factory.

   - xT plays the role of a rich type,
   - T is a new type linked to xT by some lemma. In this case a very strong
     cancellation lemma canfg
*)
Definition link {xT T : UU0} {f : xT -> T} {g : T -> xT}
                (canfg : forall x, f (g x) = x)
              :=
                 T. (* (link canfg) is convertible to T *)

(* We explain HB how to transfer Equality over link *)
Section _TransferEQ.

Context {eT : Equality.type} {T : UU0} {f : eT -> T} {g : T -> eT}.
About eT.
About T.
Context (canfg : forall x, f (g x) = x).

Definition link_eqtest (x y : T) : bool := eqtest (g x) (g y).
Check link_eqtest.
Lemma link_eqOK (x y : T) : reflect (x = y) (link_eqtest x y).
Proof.
rewrite /link_eqtest. case: (eqOK (g x) (g y)) => [E|abs].
   constructor. rewrite -[x]canfg -[y]canfg E canfg. by [].
by constructor=> /(f_equal g)/abs.
Qed.

Check link canfg.

(* (link canfg) is now an Equality instance *)
HB.instance Definition link_HasEqDec :=
  HasEqDec.Build (link canfg) link_eqtest link_eqOK.

End _TransferEQ.

End Feather.

(* Module zul. *)
HB.mixin Record IsMayProvide (ix i: interface) := {
  proj_p : forall {α}, ix α -> option (i α)
}.

HB.structure Definition MayProvide (ix : interface) :=
    { i of IsMayProvide ix i }. 

HB.mixin Record IsProvide ( ix i : interface ) of MayProvide ix i := {
  inj_p : forall {α}, i α -> ix α;
  proj_inj_p_equ :
    forall {α} (e : i α),
      proj_p α (inj_p e) = Some e
}.

HB.structure Definition Provide (ix : interface) :=
    { i of IsProvide ix i & IsMayProvide ix i }. 

HB.mixin Record CanDistinguish (ix : interface) (i : Provide.type ix) (j : MayProvide.type ix) := {
    (* P_t: Provide.type ix ;
    Mp_t : MayProvide.type ix; *)
    distinguish : forall {a} e, proj_p (s:=j) a (inj_p a (s:=i) e) = None
}.

HB.structure Definition Distinguish (ix : interface) (i : Provide.type ix) := 
    {j of CanDistinguish ix i j}.



Module rfl_m.
    Section rfl_s.
        (* Variable a : UU0. *)
        Variable i : interface.
        Variable j : interface.

Definition proj_def (a : UU0) (e : i a) : option (j a) := None.
HB.instance Definition default_MayProvide := IsMayProvide.Build i j proj_def.


Definition proj_rfl (a : UU0) (e : i a) : option (i a) := Some e.

HB.instance Definition refl_MayProvide := IsMayProvide.Build i i proj_rfl.

Definition inj_rfl (a : UU0) (e : i a) : i a := e.

Lemma proj_inj_rfl_equ : forall a e, proj_rfl a (inj_rfl a e) = Some e.
    by [].
Qed.

(* HB.about Provide_of.Build. *)

HB.instance Definition refl_Provide := IsProvide.Build i i inj_rfl proj_inj_rfl_equ.

End rfl_s.
End rfl_m.

Declare Scope interface_scope.


Module compose_m.

Inductive iplus (i j : interface) (α : UU0) :=
| in_left (e : i α) : iplus i j α
| in_right (e : j α) : iplus i j α.

Arguments in_left [i j α] (e).
Arguments in_right [i j α] (e).

Infix "+" := iplus : interface_scope.
    Section compose_left_s.

        (* Variable a : UU0. *)
        Variable ix j : interface.

        Variable pt : Provide.type ix.
        Notation i := (Provide.sort ix pt).
(* TODO: Check if feather factory helps us here *)
        Variable p_comb : Provide.type (iplus ix j).
        Notation ixj := (Provide.sort (iplus ix j) p_comb).
        (* Variable MP : MayProvide.type (iplus ix j). *)
        (* Variable P : Provide.sort ix P_t a. *)
(* Check proj_p. *)

Check p_comb.

Program Definition proj_plus_left (a : UU0) (e : ixj a) : option (i a) := _. 
Next Obligation.
move=>a _. apply:None.
    Qed.
(* Should be smth like : 
match e with
| in_left ei => proj_p a ei
| _ => None
end. *)

(* HB.instance Definition iplus_left_MayProvide := IsMayProvide.Build (iplus ix j) i proj_plus_left. *)

(* Definition inj_plus_left (a : UU0) (e : i a) : (iplus ix j) a := in_left (inj_p a e). *)

(* Lemma proj_inj_plus_left_equ : forall (a : UU0) (e : i a), proj_plus_left a (inj_plus_left a e) = Some e.
    by move=>a e; rewrite /proj_plus_left/inj_plus_left proj_inj_p_equ.
Qed. *)

(* HB.instance Definition iplus_left_Provide := IsProvide.Build (iplus ix j) i inj_plus_left proj_inj_plus_left_equ. *)

End compose_left_s.    

Section compose_right_s.

        Variable jx i : interface.

        Variable pt : Provide.type jx.
        Notation j := (Provide.sort jx pt).
(* Check proj_p. *)

Definition proj_plus_right (a : UU0) (e : (iplus i jx) a) : option (j a) := match e with
| in_right ej => proj_p a ej
| _ => None
end.

HB.instance Definition _ := IsMayProvide.Build (iplus i jx) j proj_plus_right.

Definition inj_plus_right (a: UU0) (e : j a) : (iplus i jx) a := in_right (inj_p a e).

Lemma proj_inj_plus_right_equ : forall a e, proj_plus_right a (inj_plus_right a e) = Some e.
    by move=>a e; rewrite /proj_plus_right/inj_plus_right proj_inj_p_equ.
Qed.

End compose_right_s.

(* Ltac find_may_provide := apply: refl_MayProvide*)

