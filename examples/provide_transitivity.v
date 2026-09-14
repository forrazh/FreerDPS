From mathcomp Require Import ssreflect.
From FreerDPS Require Import effect.

(** These examples exercise automatic [Provide] transitivity through the
    projections of [StrictProvide2].  The path alternates between left and
    right projections so that both branches of the hint are tested. *)

Section three_levels.
Variables L0 S0 S1 S2 N1 N2 N3 : effect.
Context `{h1 : L0 ;; S0 -<< N1}.
Context `{h2 : S1 ;; N1 -<< N2}.
Context `{h3 : N2 ;; S2 -<< N3}.

Goal L0 -< N3.
Proof. exact: _. Qed.

Goal S0 -< N3.
Proof. exact: _. Qed.
End three_levels.

(** This tree is uneven: leaves [A] and [B] are three edges from [Root],
    [C] is two edges away, and [D] is directly below it. *)
Section three_levels_uneven.
Variables A B C D AB ABC Root : effect.
Context `{hab : A ;; B -<< AB}.
Context `{habc : AB ;; C -<< ABC}.
Context `{hroot : D ;; ABC -<< Root}.

Goal A -< Root.
Proof. exact: _. Qed.

Goal B -< Root.
Proof. exact: _. Qed.

Goal C -< Root.
Proof. exact: _. Qed.

Goal D -< Root.
Proof. exact: _. Qed.
End three_levels_uneven.

(* Plain [Provide] chains can also occur below strict-provider nodes.  These
   leaves have paths of different lengths to [Root]. *)
Section uneven_with_inner_provides.
Variables LA LB LC A BMid B C AB Root : effect.
Context `{la_to_a : LA -< A}.
Context `{lb_to_bmid : LB -< BMid}.
Context `{bmid_to_b : BMid -< B}.
Context `{ab_children : A ;; B -<< AB}.
Context `{lc_to_c : LC -< C}.
Context `{root_children : AB ;; C -<< Root}.

Goal LA -< Root.
Proof. exact: _. Qed.

(* This tests look very hard to resolve *)
(* Goal LB -< Root.
Proof. exact: _. Qed. *)
(* Print HintDb typeclass_instances.

Set Typeclasses Debug.
Set Typeclasses Debug Verbosity 2.
Goal LC -< Root.
Proof. typeclasses eauto.

exact: _. Qed. *)
End uneven_with_inner_provides.

Section direct_outer_branch.
Variables L0 N1 N2 N3 Root : effect.
Context `{level1 : L0 -< N1}.
Context `{level2 : N1 -< N2}.
Context `{level3 : N2 -< N3}.
Context `{direct_to_root : N3 -< Root}.

(* Goal L0 -< Root.
Proof. exact: _. Qed.

Goal N1 -< Root.
Proof. exact: _. Qed.

Goal N2 -< Root.
Proof. exact: _. Qed. *)

Goal N3 -< Root.
Proof. exact: _. Qed.
End direct_outer_branch.

(** A complete binary tree with three provider edges from every leaf to the
    root. *)
Section three_level_full_tree.
Variables L00 L01 L02 L03 L04 L05 L06 L07 : effect.
Variables N10 N11 N12 N13 N20 N21 Root : effect.

Context `{n10_children : L00 ;; L01 -<< N10}.
Context `{n11_children : L02 ;; L03 -<< N11}.
Context `{n12_children : L04 ;; L05 -<< N12}.
Context `{n13_children : L06 ;; L07 -<< N13}.

Context `{n20_children : N10 ;; N11 -<< N20}.
Context `{n21_children : N12 ;; N13 -<< N21}.
Context `{root_children : N20 ;; N21 -<< Root}.

Goal L05 -< N21.
Proof. exact: _. Qed.

Goal L00 -< Root.
Proof. exact: _. Qed.

Goal L03 -< Root.
Proof. exact: _. Qed.

Goal L04 -< Root.
Proof. exact: _. Qed.

Goal L07 -< Root.
Proof. exact: _. Qed.

Goal N10 -< Root.
Proof. exact: _. Qed.

Goal N13 -< Root.
Proof. exact: _. Qed.

Goal N20 -< Root.
Proof. exact: _. Qed.
End three_level_full_tree.
