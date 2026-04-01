From FreerDPS Require Export Init.
From HB Require Import structures.
From mathcomp Require Import ssrfun ssrbool.

Definition interface : UU0 := (UU0 -> UU0).

(* Coercion iface : interface >-> (UU0 -> UU0). *)

Inductive iempty : interface := .

Inductive STORE (S : UU0) : interface := 
| Get : STORE S S 
| Put (s : S) : STORE S unit.

Arguments Get {S}.
Arguments Put [S] (s).

(* Module zul. *)
HB.mixin Record IsMayProvide (i ix : interface) := {
  proj_p : forall (α : UU0), ix α -> option (i α)
}.

HB.structure Definition MayProvide (i : interface) :=
    { ix of IsMayProvide i ix }. 

HB.mixin Record IsProvide ( i ix : interface ) of MayProvide i ix := {
  inj_p : forall {α : UU0}, i α -> ix α;
  proj_inj_p_equ :
    forall {α : UU0} (e : i α),
      proj_p α (inj_p e) = Some e
}.

HB.structure Definition Provide (i : interface) :=
    { ix of IsProvide i ix & IsMayProvide i ix }. 

Check proj_p.
(* 
HB.factory Record IsProvide2
  (i1 i2 ix : interface)
  of Provide i1 ix & Provide i2 ix := {
  }. *)

HB.mixin Record IsCombinedProvider (i j ix : interface) of Provide i ix := {
}.
HB.structure Definition CombinedProvider (i j : interface) := 
    {ix of IsCombinedProvider i j ix & IsProvide i ix & IsMayProvide j ix & IsMayProvide i ix }.


HB.mixin Record IsProvide2 (i j ix : interface) of Provide i ix & Provide j ix := {
}.

HB.structure Definition Provide2 (i j : interface) := 
    {ix of IsProvide2 i j ix 
        & Provide j ix & MayProvide j ix
        & Provide i ix & MayProvide i ix 
     }.

Check Provide2.Interface_IsMayProvide_mixin.

Check proj_p.


(* HB.structure Definition Provide2 (i1 i2 : interface) := *)
  (* { ix of IsProvide2 i1 i2 ix &}. *)

(* HB.about IsProvide2.Build. *)


    (* proj_p_i : forall (α : UU0) (e : ix α), proj_p (s:=MayProvide.type i) α e *)

(* HB.structure Definition MultiProvider (i j : interface) :=  *)
    (* {ix of IsMultiProvider i j ix & IsProvide i ix & IsMayProvide i ix & IsProvide j ix & IsMayProvide j ix }. *)

(* HB.about IsMultiProvider.Build. *)

Section t.
    Variables (i j : interface) (ix : Provide2.type i j).
    Variables (α : UU0) (e : i α).
Check inj_p.
(* 
inj_p
     : forall α0 : UU0, ?i α0 -> ?s α0
where
?i : [i : interface j : interface ix : Provide2.type i j α : UU0 e : i α |- interface]
?s : [i : interface j : interface ix : Provide2.type i j α : UU0 e : i α
|- Provide.type ?i]
*)
Check inj_p (s:=ix).
(* 
inj_p
     : forall α : UU0, j α -> ix α
 *)
Fail Check proj_p (s:=ix) (i:=i).
(* 
The command has indeed failed with message:
In environment
i, j : interface
ix : Provide2.type i j
α : UU0
e : i α
The term "ix" has type "Provide2.type i j" while it is expected to have type
"MayProvide.type i".
*)
(* HB.mixin Record CanDistinguish (i j : interface) (ix : CombinedProvider.type i j) : Prop := {
    (* P_t: Provide.type ix ;
    Mp_t : MayProvide.type ix; *)
    distinguish : forall {α : UU0} (e : i α), proj_p (i:=j) α (inj_p α (s:=ix) e) = None
}. *)

HB.about Provide2.
(* 
HB: Provide2.type is a structure (from "(stdin)", line 3)
HB: Provide2.type characterizing operations and axioms are:
HB: Provide2 is a factory for the following mixins:
    - IsMayProvide
    - IsProvide
    - IsProvide2 (* new, not from inheritance *)
HB: Provide2 inherits from:
    - MayProvide
    - Provide
HB: Provide2 is inherited by:
*)

HB.about MayProvide.
(* 
HB: MayProvide.type is a structure (from "(stdin)", line 19)
HB: MayProvide.type characterizing operations and axioms are:
    - proj_p
HB: MayProvide is a factory for the following mixins:
    - IsMayProvide (* new, not from inheritance *)
HB: MayProvide inherits from:
HB: MayProvide is inherited by:
    - Provide
    - CombinedProvider
    - Provide2
*)

(* HB.structure Definition Distinguish (ix : interface) (i : Provide.type ix) :=  *)
    (* { j of CanDistinguish ix i j }. *)

(* Check CanDistinguish.distinguish. *)
(* About Distinguish.Interface_CanDistinguish_mixin. *)
End t.

Module rfl_m.
    Section df.
    (* Variable a : UU0. *)
    Context {i j : interface}.
        (* Variable i : interface. *)
        (* Variable j : interface. *)

Definition proj_def (a : UU0) (e : i a) : option (j a) := None.
HB.instance Definition default_MayProvide := IsMayProvide.Build j i proj_def.
    End df.

    Section rfl_s.
        Variable i : interface.

Definition proj_rfl (a : UU0) (e : i a) : option (i a) := Some e.

HB.instance Definition refl_MayProvide := IsMayProvide.Build i i proj_rfl.

Definition inj_rfl (a : UU0) (e : i a) : i a := e.

Lemma proj_inj_rfl_equ : forall a e, proj_rfl a (inj_rfl a e) = Some e.
    by [].
Qed.

(* HB.about Provide_of.Build. *)

HB.instance Definition refl_Provide := IsProvide.Build i i inj_rfl proj_inj_rfl_equ.
About proj_def.
Lemma dist : forall (a : UU0) e, proj_def (j:=i) a (inj_rfl a e) = None.
Proof.
    move => a e.
    by rewrite/proj_def.
Qed.

HB.graph graph.f.

HB.instance Definition refl_Dist := CanDistinguish.Build i i j dist.

End rfl_s.
End rfl_m.

Declare Scope interface_scope.


Module compose_m.


Inductive iplus (i j : interface) (α : UU0)  := 
| in_left (e : i α) : iplus i j α 
| in_right (e : j α) : iplus i j α.


(* Inductive iplus (i j : interface) (α : UU0) : interface α :=
| in_left (e : i α) : iplus i j α
| in_right (e : j α) : iplus i j α. *)

Arguments in_left [i j α] (e).
Arguments in_right [i j α] (e).

Infix "+" := iplus : interface_scope.

Section compose_left_s.

    Context {ix j : interface}.
    (* Context {pJ : MayProvide.type ix}. *)
    (* Definition j : interface := (MayProvide.sort ix pJ). *)
    Notation ixj := (iplus ix j).
    Context {pT : Provide.type (ix)}.
    Context {α : UU0}.
    Definition i : interface := (Provide.sort (ix) pT).
    (* Context {a : UU0} {f : pS a -> ixj a} {g : ixj a -> pS a}. *)
    (* Context (canfg : forall e, f (g e) = e).  *)

Check ixj.
    
Definition proj_plus_left : forall α, ixj α -> option (i α) := fun α e => match e with 
| in_left e_l => proj_p (s:=i) α e_l
| _ => None
end.

Check ixj.

(* #[non_forgetful_inheritance] *)
HB.instance Definition iplus_left_MayProvide := IsMayProvide.Build ixj i proj_plus_left.

Definition inj_plus_left (a: UU0) (e : i a) : ixj a := in_left (inj_p (s:=i) a e).

Lemma proj_inj_plus_left_equ : forall (a:UU0) (e: i a), proj_plus_left a (inj_plus_left a e) = Some e.
    move=>a e; rewrite /proj_plus_left/inj_plus_left. exact/proj_inj_p_equ.
Qed.

HB.instance Definition iplus_left_Provide := IsProvide.Build ixj i inj_plus_left proj_inj_plus_left_equ.

Check rfl_m.proj_def.

End compose_left_s.

Section compose_right_s.

    Context {i jx : interface}.
    Notation ijx := (iplus i jx).
    Context {pT : Provide.type (jx)}.
    Let j : interface := (Provide.sort (jx) pT).
    (* Context {a : UU0} {f : pS a -> ixj a} {g : ixj a -> pS a}. *)
    (* Context (canfg : forall e, f (g e) = e).  *)

Definition proj_plus_right (a : UU0) (e : ijx a) : option (j a) := match e with 
| in_right e_r => proj_p (s:=j) a e_r
| _ => None
end.

(* #[non_forgetful_inheritance] *)
HB.instance Definition iplus_right_MayProvide := IsMayProvide.Build ijx j proj_plus_right.

Definition inj_plus_right (a: UU0) (e : j a) : ijx a := in_right (inj_p (s:=j) a e).

Let proj_inj_plus_right_equ : forall (a:UU0) (e: j a), proj_plus_right a (inj_plus_right a e) = Some e.
    move=>a e; rewrite /proj_plus_right/inj_plus_right. exact/proj_inj_p_equ.
Qed.

HB.instance Definition iplus_right_Provide := IsProvide.Build ijx j inj_plus_right proj_inj_plus_right_equ.

Check compose_m_j__canonical__Interface_Provide.

End compose_right_s.
End compose_m.

HB.export compose_m.

Check inj_plus_left.

Module distinctions.

    Section dist_s.



        Context {ix jx : interface}.
        Notation ixjx := (iplus ix jx).

        Search Provide.type.

Check Provide.Pack _ _ iplus_left_Provide.
Check @iplus_left_Provide.

Check @compose_m_i__canonical__Interface_Provide ix jx.


        Print Provide.type.

        Context {pI : Provide.type ix} {pJ : Provide.type jx}.
        Definition i : interface := Provide.sort ix pI.

Definition prov :=  @compose_m_i__canonical__Interface_Provide ix jx i.
Check compose_m.i.
Check prov.
        Definition j : interface := Provide.sort jx pJ.


Lemma dist : forall (a : UU0) e, rfl_m.proj_def _ j a (inj_plus_left (j:=jx) (pT:= prov) a e) = None.
Proof.
    move => a e.
    by rewrite/rfl_m.proj_def.
Qed.


HB.about CanDistinguish.Build.

HB.instance Definition refl_Dist := CanDistinguish.Build ixjx prov prov dist.
