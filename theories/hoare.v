(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From HB Require Import structures.
From mathcomp Require Import boot functions boolp classical_sets.
From monae Require Import hierarchy.
From FreerDPS Require Import mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** To reason about impure computations, we introduce the “Hoare
    monad,” also called the “specification monad.” An instance of the
    specification monad is a couple of [pre] and [post] conditions,
    such that [pre p T] means the program specified by [p] can be
    executed safely from a state [T], and [post p T x T'] means the
    execution of [p] from [T] may compute a result [x] and bring the
    system to a state [T'].

    We equip this couple of predicate with a [bind] function to
    sequentially compose specifications. *)

Local Open Scope classical_set_scope.
Local Open Scope monae_scope.
(* model *)
Module Hoare.
(* Section tmp. *)

(* Context {T : UU0} {M : stateMonad T} {U : UU0}. *)

(* Variable triple :
  forall U : UU0, *)

(* Definition Pre := set T. *)
(* Definition Post (U : UU0) := T -> U -> set T. *)
(* Program Definition HoareState (pre : Pre) {U : UU0} (post : Post U) : UU0 *)
(* := *)
  (* {m : M U | *)
    (* forall initial, pre initial -> *)
      (* triple (fun s => s = initial) m (post initial)}. *)

(* Definition top := fun x:T => True. *)

(* Program Definition re (U : UU0) *)
(* : forall x , @HoareState top U (fun i y f => i = f /\ y = x ) := _. *)
(* Next Obligation. move=>A a /=. apply: (proj1_sig). apply: Ret. Qed. *)

(* Check HoareState. *)
(* End tmp. *)



Record hoare T U : Type := mk_hoare {
  pre : set T ;
  (* prog : M U  ; *)
  post : T -> U -> set T }.
(* End tmph. *)



Arguments mk_hoare {T  U} (pre post).
Arguments pre {T  U} (_ _).
(* Arguments prog {T M U} _. *)
Arguments post {T  U} (_ _ _).
HB.about stateRunMonad.


(* Section tmp.  *)
(* Context T U {M : stateMonad T} (triple : set T -> M U -> (U -> set T) -> Prop). *)
Definition hoare_ret {T} {U : UU0} (x : U) : @hoare T U :=
  mk_hoare [set: T] (fun s y s' => (x = y) /\ (s = s')).

Definition hoare_bind {T} {U V}
    (m : hoare T U) (k : U -> hoare T V) : hoare T V := mk_hoare
    (fun s => pre m s /\ (forall x, post m s x `<=` pre (k x)))
    (fun s x s2 => exists y s', post m s y s' /\ post (k y) s' x s2).

Inductive valid_hoare {T : UU0} {N : monad} {M: stateRunMonad T N} {U : UU0}
    (h : hoare T U) (m : M U) : Prop :=
| correct_hoare : (forall s, pre h s ->
  (forall a s', (runStateT m s = Ret (a, s')) -> post h s a s')) ->
  valid_hoare h m.

Notation "{{ pre }} prog {{ post }}" := (valid_hoare (@mk_hoare _ _ pre post) prog)
  (at level 90,
   format "'[' '[' {{  pre  }}  ']' '/ ' '['  prog ']' '['  {{  post  }} ']' ']'")
.
Check correct_hoare.
Check forall x, pre (hoare_ret x).

Section tmp.
Hypothesis injective_return : forall (M : monad) (C : Type) (x1 x2 : C),
  Ret x1 = (Ret x2 :> M C) -> x1 = x2.

Lemma valid_ret {T: UU0} {U : UU0} {N : monad} {M : stateRunMonad T N} (x : U)
  : @valid_hoare T N M U (@hoare_ret T U x) (Ret x).
apply: correct_hoare => //=.
move=> s P u s'.
HB.about stateRunMonad.
rewrite runStateTret /==> Hret.
by have [] := @injective_return N (U * T) (x,s) (u,s') Hret.
Qed.

Lemma valid_bind {T: UU0} {U V : UU0} {N : monad} {M : stateRunMonad T N}
  (h : hoare T U) ( m : M U) (h' : U -> hoare T V) (k : U -> M V)
  : @valid_hoare T N M V (hoare_bind h h' ) (m >>= k).
Proof.
apply: correct_hoare=> //=.
move=> s [Hpr Hpo] v s'.
Search runStateT.
rewrite runStateTbind /=.
(* case: (runStateT m s). *)
(* exists . *)
Admitted.
End tmp.

Section hm.
Context (T : UU0).
 (* {M : stateMonad T}. *)
Let ret := @hoare_ret T.
Let bind := @hoare_bind T.

Let right_neutral : BindLaws.right_neutral bind ret.
Proof.
move=> A [pr po].
rewrite /bind /ret /hoare_bind /hoare_ret/=; congr mk_hoare.
- by apply/seteqP; split => // s [].
(* - exact: bindmret. *)
- apply/eq3_fun => s a s''.
  under eq2_exists do rewrite andA.
  by rewrite ex2C ex2_eqr ex_eqr.
Qed.

(* Local Open Scope ssripat_scope. *)

Let left_neutral : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind /ret /hoare_bind /hoare_ret/=.
move fa : (f a) => [pr po]; congr mk_hoare.
- apply/funext=> s; rewrite andTP; apply/propext; split.
  + by move=> /(_ a s); rewrite fa/=; exact.
  + by move=> prs _ _ [<- <-]; rewrite fa.
(* - by rewrite bindretf fa. *)
- apply/eq3_fun => s b s'.
  under eq2_exists do rewrite andC andA.
  rewrite ex2C.
  under eq_exists do rewrite ex_andl.
  by rewrite ex_eqr_sym ex_eqr_sym fa.
Qed.

Let assoc : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind /ret /hoare_bind /hoare_ret/=.
case: m => prA poA/=; congr mk_hoare.
- apply/funext => s; apply/propext; split.
  + move=> [[prAs poApre postpre]].
    split => // a s1 sas1; split=> [|b s2 s'bs2].
      exact: poApre.
    by apply: postpre; exists a, s1.
  + move=> [prAs poApre]; split.
      by split=> // a s1 /poApre[].
    move=> b s1 [x [s2]] [] /poApre [fxs2] /[swap] s2bs1.
    exact.
(* - exact: bindA. *)
- apply: eq3_fun => s c s1.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => a.
  under eq2_exists do rewrite -ex_andl.
  rewrite ex3C; apply: eq_exists => s2.
  rewrite -ex_andr.
  under [in RHS]eq_exists do rewrite -ex_andr.
  by under [in RHS]eq2_exists do rewrite andA.
Qed.

HB.instance Definition _ := isMonad_ret_bind.Build (hoare T)
  left_neutral right_neutral assoc.

End hm.

End Hoare.

(** ** Monad *)

(** Easier to had future laws from there. *)
(*
HB.mixin Record isMonadHoare (S : Type) (ST : stateMonad S)
    (M : Type -> Type) of Monad M := {
      ht : forall (A: UU0) (m : M A), Prop ;
      ht_bind (A B : UU0) (m : M A) (k : A -> M B) :
        ht _ m -> (forall x, ht _ (k x)) -> ht _ (m >>= k) ;

      wp: forall (A: UU0) (m : M A) (Q : A -> set S), set S ;

      wp_ret : forall (A: UU0) (a : A) (Q : A -> set S), wp A (Ret a) Q = Q a;
      wp_bind : forall (A B : UU0) (m : M A) (k : A -> M B) (Q : B -> set S),
        wp _ (m >>= k) Q = wp _ m (fun x s=> wp _ (k x) Q s)
    }.

#[short(type=hoareMonad)]
HB.structure Definition MonadHoare (S : Type) (ST : stateMonad S) :=
  {M of isMonadHoare S ST M &}. *)

HB.export Hoare.
From monae Require Import monad_model monad_transformer.

Module TestM.
Section st.

Context {S : UU0}.

Let N : monad := option_monad.
Definition M : stateMonad S := [the stateMonad S of stateT S N].
(* Notation ms := (StateMonad.acto S). *)

HB.about stateRunMonad.
Notation hs := (hoare S).

(* Definition ht *)
  (* (A : Type) (h: hs A) (m: M A) : Prop := valid_hoare h m. *)

Definition wp (A : UU0) (h: hs A) (m: M A) (Q : A -> set S) : set S
 :=
fun s=> match runStateT m s with
| inr (a, s') => post h s a s' -> Q a s'
| inl _ => True
end.

(* fun s=> match prog m s with *)
(* | (a, s')=> Q a s' *)
(* end. *)

(* Lemma ht_bind (A B : UU0) (m : hs A) (k : A -> hs B) (p: M A) :
  ht m -> (forall x, ht (k x)) -> ht (m >>= k).
Proof.
move=> Hm Hk s; move: Hm.
case: m s=> /= pr pg po s + [Hpr Hpo]=> /(_ s Hpr) /=.
rewrite state_bindE /comp /uncurry.
case: (pg s) => a s' Hm.
move: Hpo=> /(_ a s' Hm) Hpo.
move: Hk=> /(_ a s' Hpo).
case: (prog (k a)) => Hprk Hpg Hpok /=.
by exists a, s'.
Qed. *)

(* Lemma wp_ret (A : UU0) (x : A) (Q : A -> S -> Prop) : *)
  (* wp (Ret x) Q = Q x. *)
(* Proof. done. Qed. *)
(*  *)
(* Lemma wp_bind (A B : UU0) (m : hs A) (k : A -> hs B) *)
    (* (Q : B -> S -> Prop) : *)
  (* wp (m >>= k) Q = wp m (fun x s => wp (k x) Q s). *)
(* Proof. *)
(* rewrite /wp; apply: funext=>s /=. *)
(* rewrite state_bindE /comp /uncurry. *)
(* by case : prog. *)
(* Qed. *)
(*  *)
(* HB.about isMonadHoare.Build. *)
(*  *)
(* HB.instance Definition _ := isMonadHoare.Build S ms hs ht_bind wp_ret wp_bind. *)
End st.
End TestM.
Export TestM.
(* machinery to reason about WP / SP *)
(* if I remember correctly, we need the consequence rules:
- a weaken law and
- a strengthen law *)
(* Section hoare_state. *)
(* Context {S : UU0} {M : stateMonad S}.
Definition top : set S := fun s => True.
Definition hget : hoare M S := {{top}} get {{ fun s x s' => s = s' /\ x = s}}.
Definition hput (x : S) : hoare M unit := {{top}} put x {{fun _ _ f => f = x}}.
End hoare_state.

(* Section hoare_acto. *)
Context {S : UU0}.
Notation ms := (StateMonad.acto S).
Notation hs := (hoare ms).


Context {A : UU0}.
Lemma consq {P P' : set S} (c : ms A ) {Q Q' : S -> A -> set S} :
(forall i, P' i -> P i) -> (forall i x f , Q i x f -> Q' i x f ) ->
 ht ({{P}} c {{Q}}) -> ht ({{P'}} c {{Q'}}).
Proof.
move=> str wkn + s /= pr=> /(_ s) /=.
move: str=>/(_ s pr) str /(_ str).
by case: c; exact: wkn.
Qed.

Lemma weaken {P : set S} (m : hs A) :
ht m -> (forall s, P s -> pre m s) -> ht ({{ P }} prog m {{ post m }}).
Proof.
move=> Hm Hp.
apply: consq.
- exact: Hp.
- move=> s a s'; exact.
- exact: Hm.
Qed.

Lemma strengthen (m : hs A)
(Q : S -> A -> S -> Prop) :
ht m -> (forall s a s', post m s a s' -> Q s a s') -> ht ({{ pre m }} prog m {{ Q }}).
Proof.
move=> Hm Hp.
apply: consq.
- move=> s Hpr. exact: Hpr.
- exact: Hp.
- exact: Hm.
Qed.

Lemma wp_precondition (m : hs A) (Q : A -> S -> Prop) :
ht ({{fun s=> wp m (post m s) s }} prog m {{ post m }}).
Proof. done. Qed.

Lemma wp_weakest (m : hs A) :
ht m -> forall s, pre m s -> wp m (post m s) s .
Proof. done. Qed.

Lemma wp_get (Q : S -> S -> Prop) :
  wp (hget) Q = (fun s => Q s s).
Proof. done. Qed.

Lemma wp_put (s' : S) (Q : unit -> S -> Prop) :
  wp (hput s') Q = (fun _ => Q tt s').
Proof. done. Qed.

Definition incr : hoare (StateMonad.acto nat) nat := (hget >>= fun s=> hput (s + 1) >> hget). *)
(* End hoare_acto. *)

From FreerDPS Require Import effect freer contract.

HB.mixin Record isContractSpecifier (S : Type) {Fx F : effect} `{F -<? Fx}
    (M : Type -> Type) of MonadState S M := {
      state_of_contract : forall (c : contract F S), Fx ~~> M ;
      (* hoare_of_contract : forall (c : contract F S), Fx ~~> M *)
    }.

#[short(type=specMonad)]
HB.structure Definition MonadSpec (S : Type) {Fx F : effect} `{Hf: F -<? Fx} :=
  {M of isContractSpecifier S Fx F Hf M &}.

  (* -------------------------------------------------------------------------- *)


Module Tust.
Section tmp.
Context {S : UU0} {Fx F : effect} `{F -<? Fx}.
Notation ms := (StateMonad.acto S).
Notation hs := (hoare ms).

Definition soc : forall (c : contract F S), Fx ~~> ms.
move=> c A cmd s.
apply: (_, _).
- admit.
- apply: gen_state_update.
  + apply: H.
  + apply: c.
  + apply: s.
  - apply: cmd.

Check gen_state_update.
Admitted.

HB.instance Definition _ := isContractSpecifier.Build S Fx F H ms soc.
End tmp.
End Tust.
Export Tust.
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
HB.about stateMonad.
Section tmp.
Context {S : UU0}.
(* Notation ms := (StateMonad.acto S). *)

(* Definition hoare_of_contract {Fx F : effect} `{H: F -<? Fx} {MS : specMonad S H}  (c : contract F S) : Fx ~~> hoare MS
  := fun U cmd =>
  {{gen_requirement c ^~ cmd}}
    state_of_contract c _ cmd
  {{fun s u s' => s' = gen_state_update c s cmd u /\ gen_promise c s cmd u}}. *)

Axiom state_update' : forall [F : effect] [T : UU0],
contract F T -> T -> forall [U : UU0] {M : stateMonad T}, F U -> U -> M U.
Definition gen_state_update' {S} (M : stateMonad S) {X : UU0} {Fx F : effect} `{F -<? Fx}
    (c : contract F S)
    (s : S) (cmd : Fx X) (x : X)
  : M X :=
  if prj cmd is Some cmd then state_update' c s cmd x else Ret x.
Section hoare_freer.

Check make_contract.


Context {Fx F : effect} `{F -<? Fx} (T : Type) (c : contract F T).
Context {M : stateMonad T}.
Notation ms := (StateMonad.acto T).
Notation hs := (hoare ms).
Print store_update .

Arguments gen_state_update' : simpl never.

