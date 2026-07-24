(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(**md**************************************************************************)
(* # Temporary logical lemmas awaiting inclusion in MathComp                  *)
(*                                                                            *)
(* TODO: Move to MCA                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*        eq4_exists == congruence under four existential quantifiers         *)
(*              andTP == remove `True` from the left of a conjunction         *)
(*               ex2C == exchange two existential quantifiers                 *)
(*               ex3C == exchange the first and third quantifiers             *)
(*              ex3AC == exchange the second and third quantifiers            *)
(*            ex_andl == distribute an existential over a right conjunction   *)
(*            ex_andr == distribute an existential over a left conjunction    *)
(*             ex_eqr == eliminate a right equality witness                   *)
(*         ex_eqr_sym == eliminate a symmetric right equality witness         *)
(*            ex2_eqr == eliminate an equality under two existentials         *)
(*        ex2_eqr_sym == symmetric version of `ex2_eqr`                       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

From FreerDPS Require Import Init.
From mathcomp Require Import all_boot.

Lemma eq4_exists T S R N
  (U V : forall (x : T) (y : S x) (z : R x y), N x y z -> Prop) :
  (forall x y z n, U x y z n = V x y z n) ->
  (exists x y z n, U x y z n) = (exists x y z n, V x y z n).
Proof. by move=> UV; apply/eq3_exists => x y z; exact/eq_exists. Qed.

Lemma andTP (P : Prop) : (True /\ P) = P.
Proof. by apply/propext; split => // -[]. Qed.

Lemma ex2C A B (P : A -> B -> Prop) :
  (exists a b, P a b) = (exists b a, P a b).
Proof. by apply/propeqP; split=> -[x [y xy]]; [exists y, x | exists y, x]. Qed.

Lemma ex3C A B C (P : A -> B -> C -> Prop) :
  (exists a b c, P a b c) = (exists c b a, P a b c).
Proof.
apply/propeqP; split=> -[x [y [z xyz]]].
  by exists z, y, x.
by exists z, y, x.
Qed.

Lemma ex3AC A B C (P : A -> B -> C -> Prop) :
  (exists a b c, P a b c) = (exists a c b, P a b c).
Proof.
apply/propeqP; split=> [[a [b [c abc]]] | [a [c [b abc]]]].
  by exists a, c, b.
by exists a, b, c.
Qed.

Lemma ex_andl A (P : A -> Prop) (Q : Prop) :
  (exists a, P a /\ Q) = ((exists a, P a) /\ Q).
Proof.
apply/propeqP; split=> [[a [Pa q]] | [[a Pa] q]].
  by split=> //; exists a.
by exists a.
Qed.

Lemma ex_andr A (P : Prop) (Q : A -> Prop) :
  (exists a, P /\ Q a) = (P /\ (exists a, Q a)).
Proof.
under eq_exists do rewrite andC.
by rewrite ex_andl andC.
Qed.

Lemma ex_eqr A (a' : A) (P : A -> Prop) :
  (exists a, P a /\ a = a') = P a'.
Proof. by apply/propeqP; split=> [[a [Pa <-//]] | Pa']; exists a'. Qed.

Lemma ex_eqr_sym A (a' : A) (P : A -> Prop) :
  (exists a, P a /\ a' = a) = P a'.
Proof. by apply/propeqP; split=> [[a [Pa ->//]] | Pa']; exists a'. Qed.

Lemma ex2_eqr A B (a' : A) (P : A -> B -> Prop) :
  (exists a b, P a b /\ a = a') = (exists b, P a' b).
Proof. by rewrite ex2C; apply: eq_exists => b; rewrite ex_eqr. Qed.

Lemma ex2_eqr_sym A B (a' : A) (P : A -> B -> Prop) :
  (exists a b, P a b /\ a' = a) = (exists b, P a' b).
Proof. by rewrite ex2C; apply: eq_exists => b; rewrite ex_eqr_sym. Qed.
