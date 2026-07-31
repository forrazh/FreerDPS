From mathcomp Require Import all_boot boolp ssrnum.
From HB Require Import structures.
From monae Require Import preamble hierarchy monad_lib.
From FreerDPS Require Import Init effect freer.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope nat_scope.

#[short(type=itreeMonad)]
HB.structure Definition MonadInteractionTree (F: effect) := {M of MonadFreer F M & MonadElgot M}.

Module Import ITreeModelM.
Section itree_sec.

Context {E : Type -> Type} {R : Type}.

Variant itreeF (itree : Type) :=
| pureF (r : R)
| tauF (t : itree)
| impureF {X : Type} (e : E X) (k : X -> itree).

  (** We define non-recursive types such as [itreeF] using the [Variant]
      command. The main practical difference from [Inductive] is that
      [Variant] does not generate any induction schemes (which are
      unnecessary). *)

CoInductive itree : Type := go { _observe : itreeF itree }.

End itree_sec.
End ITreeModelM.

Declare Scope itree_scope.
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.

Notation itree' E R := (itreeF E R (itree E R)).
Definition observe {E R} (t : itree E R) : itree' E R := @_observe E R t.

Notation pure x := (go (pureF _ x)).
Notation tau t := (go (tauF t)).
Notation impure e k := (go (impureF e k)).

Module Import ITreeHelperM.
Section itree_sec.
Context {F : effect}.


Local Notation M := (itree F).

CoInductive strongBisim (A : UU0) : M A -> M A -> Prop :=
| sBrefl (m : M A) : strongBisim m m
| sBLater (m m' : M A) :
  strongBisim m m' -> strongBisim (tau m) (tau m')
| sBImp {B} {op} (k k' : B -> M A) :
  (forall x, strongBisim (k x) (k' x)) ->
  strongBisim (impure op k) (impure op k').

Lemma ITreeE (A : UU0) (m : M A) : m = match m with
                                       | pure x => pure x
                                       | tau m' => tau m'
                                       | impure op k => impure op k
                                       end.
Proof. by case: m; case. Qed.

#[deprecated(note = "non standard axiom for strong bisimilarity (from monae)")]
Axiom strongBisim_eq : forall A (m m' : M A), strongBisim m m' -> m = m'.

End itree_sec.
End ITreeHelperM.

Global Arguments strongBisim {F} [A].
Global Arguments sBLater {F} [A].
Global Arguments sBImp {F} [A] {B op}.

Module Import ITreeMonadModelM.
Section itree_sec.
Context {F : effect}.
Local Notation M := (itree F).

Definition it_ret : idfun ~~> M := fun _ x => go (pureF _ x).
Let _bind [A B] (f : A -> M B) : M A -> M B := cofix aux m : M B :=
match observe m with
| pureF x => f x
| tauF m' => tau (aux m')
| impureF _ op k => impure op (fun y=>aux (k y))
end.

Definition it_bind [A B] (m : M A) (f : A -> M B) : M B := _bind f m.

Local Notation "m >>= f" := (it_bind m f) : monae_scope.

CoFixpoint right_neutral_bisim A (m : M A) : strongBisim (m >>= @it_ret A) m.
Proof.
case: m; case=> [a|m|Y op k]; rewrite [X in strongBisim X]ITreeE /=.
- exact: sBrefl.
- by apply: sBLater; exact: right_neutral_bisim.
- exact: sBImp.
Qed.

CoFixpoint associative_bisim A B C (m : M A) (f : A -> M B) (g : B -> M C) :
  strongBisim ((m >>= f) >>= g) (m >>= (fun x => f x >>= g)).
Proof.
case: m; case=> [a|m|Y op k];
  rewrite [X in strongBisim _ X]ITreeE [X in strongBisim X]ITreeE /=.
- exact: sBrefl.
- by apply: sBLater;exact: associative_bisim.
- exact: sBImp.
Qed.

Let left_neutral : BindLaws.left_neutral it_bind it_ret.
Proof. by move=> *; rewrite [LHS]ITreeE [RHS]ITreeE. Qed.

Let right_neutral : BindLaws.right_neutral it_bind it_ret.
Proof. by move=> *; exact/strongBisim_eq/right_neutral_bisim. Qed.

Let associative : BindLaws.associative it_bind.
Proof. by move=> *; exact/strongBisim_eq/associative_bisim. Qed.

#[export]
HB.instance Definition _ := isMonad_ret_bind.Build M
  left_neutral right_neutral associative.

End itree_sec.
End ITreeMonadModelM.

Module Import ITreeWBisimModelM.
Section itree_sec.
Context {F : effect}.
Local Notation M := (itree F).

Inductive tau_steps [A : UU0] : M A -> M A -> Prop :=
| ts_refl (t : M A) : tau_steps t t
| ts_tau (t u : M A) : tau_steps t u -> tau_steps (tau t) u.

CoInductive eutt [A B : UU0] [RR : A -> B -> Prop] :
    M A -> M B -> Prop :=
| euttRet (t1 : M A) (t2 : M B) (a : A) (b : B) :
    tau_steps t1 (pure a) ->
    tau_steps t2 (pure b) ->
    RR a b ->
    eutt t1 t2
| euttTau (t1 : M A) (t2 : M B) :
    eutt t1 t2 ->
    eutt (tau t1) (tau t2)
| euttImpure X (op : F X) (k1 : X -> M A) (k2 : X -> M B)
    (t1 : M A) (t2 : M B) :
    tau_steps t1 (impure op k1) ->
    tau_steps t2 (impure op k2) ->
    (forall x, eutt (k1 x) (k2 x)) ->
    eutt t1 t2.

Local Notation "x ≊ y" := (@eutt _ _ eq x y) (at level 70).

CoFixpoint eutt_refl A (a : M A) : a ≊ a.
Proof.
by case: a=> [[*|*|*]];
  [apply: euttRet | apply: euttTau | apply: euttImpure ]; eauto;
  exact: ts_refl.
Qed.

CoFixpoint eutt_sym A (a b : M A) :
    a ≊ b -> b ≊ a.
Proof.
by case=> *; [apply: euttRet | apply: euttTau | apply: euttImpure ]; eauto.
Qed.

CoFixpoint eutt_tauL A B (RR : A -> B -> Prop)
    (t1 : M A) (t2 : M B) :
    @eutt _ _ RR t1 t2 -> @eutt _ _ RR (tau t1) t2.
Proof.
case=> [u1 u2 a b u1a u2b ab
       |u1 u2 u12
       |X op k1 k2 u1 u2 u1k u2k k12].
- apply: euttRet.
  + exact/ts_tau/u1a.
  + exact: u2b.
  + exact: ab.
- apply: euttTau.
  exact: eutt_tauL u12.
- apply: euttImpure.
  + exact/ts_tau/u1k.
  + exact: u2k.
  + exact: k12.
Qed.

CoFixpoint eutt_tauR A B (RR : A -> B -> Prop)
    (t1 : M A) (t2 : M B) :
    @eutt _ _ RR t1 t2 -> @eutt _ _ RR t1 (tau t2).
Proof.
case=> [u1 u2 a b u1a u2b ab
       |u1 u2 u12
       |X op k1 k2 u1 u2 u1k u2k k12].
- apply: euttRet.
  + exact: u1a.
  + exact/ts_tau/u2b.
  + exact: ab.
- apply: euttTau.
  exact: eutt_tauR u12.
- apply: euttImpure.
  + exact: u1k.
  + exact/ts_tau/u2k.
  + exact: k12.
Qed.

Lemma tau_steps_closed A (P : M A -> Prop)
    (tau_closed : forall t, P t -> P (tau t))
    (t t' : M A) :
  tau_steps t t' -> P t' -> P t.
Proof. by elim=> [u|u1 u2 u12 /[apply]] //; exact: tau_closed. Qed.

Lemma tau_steps_euttL A B (RR : A -> B -> Prop)
    (t1 t1' : M A) (t2 : M B) :
  tau_steps t1 t1' -> @eutt _ _ RR t1' t2 -> @eutt _ _ RR t1 t2.
Proof.
by apply: (@tau_steps_closed A (fun t => @eutt _ _ RR t t2))=>?; exact: eutt_tauL.
Qed.

Lemma tau_steps_euttR A B (RR : A -> B -> Prop)
    (t1 : M A) (t2 t2' : M B) :
  tau_steps t2 t2' -> @eutt _ _ RR t1 t2' -> @eutt _ _ RR t1 t2.
Proof.
by apply: (@tau_steps_closed B (fun t => @eutt _ _ RR t1 t))=>?; exact: eutt_tauR.
Qed.

Lemma bind_tau A B (t : M A) (f : A -> M B) :
  tau t >>= f = tau (t >>= f).
Proof. by rewrite [LHS]ITreeE. Qed.

Lemma bind_impure A B X (op : F X) (k : X -> M A)
    (f : A -> M B) :
  impure op k >>= f = impure op (fun x => k x >>= f).
Proof. by rewrite [LHS]ITreeE. Qed.

Lemma tau_steps_bind A B (t1 t2 : M A) (f : A -> M B) :
  tau_steps t1 t2 -> tau_steps (t1 >>= f) (t2 >>= f).
Proof.
elim=> [u|u1 u2 u12 ih].
  exact: ts_refl.
by rewrite bind_tau; exact/ts_tau.
Qed.

Lemma tau_steps_bind_ret A B (t : M A) (a : A) (f : A -> M B) :
  tau_steps t (pure a) -> tau_steps (t >>= f) (f a).
Proof.
move=> ta.
have tf := tau_steps_bind f ta.
by rewrite bindretf in tf.
Qed.

Lemma tau_steps_bind_impure A B X (t : M A) (op : F X)
    (k : X -> M A) (f : A -> M B) :
  tau_steps t (impure op k) ->
  tau_steps (t >>= f) (impure op (fun x => k x >>= f)).
Proof.
move=> tk.
have tf := tau_steps_bind f tk.
by rewrite bind_impure in tf.
Qed.

Lemma tau_steps_assoc A (t t1 t2 : M A) :
  tau_steps t t1 -> tau_steps t t2 ->
  tau_steps t1 t2.
Admitted.

Lemma eutt_ret_steps A (t1 t2 : M A) (x : A) :
  tau_steps t1 (pure x) -> t1 ≊ t2 ->
  tau_steps t2 (pure x).
Admitted.

Lemma eutt_impure_steps A X (t1 t2 : M A) (op : F X)
    (k1 : X -> M A) :
  tau_steps t1 (impure op k1) -> t1 ≊ t2 ->
  exists2 k2, tau_steps t2 (impure op k2) &
    forall x, (k1 x) ≊ (k2 x).
Admitted.

CoFixpoint eutt_trans A (a b c : M A) :
    a ≊ b -> b ≊ c -> a ≊ c.
Proof.
case=> [t1 t2 x y t1x t2y xy
       | t t' H
       |X op k1 k2 t1 t2 t1k t2k k12] t2c.
- by subst y; apply: euttRet; eauto; exact: eutt_ret_steps t2c.
- inversion t2c as [???? t2ret cret | |????? oui t2imp cimp Himp]; subst.
  + inversion t2ret as [| ? ? tret ]; subst; apply: euttRet=>//.
    * apply: ts_tau; apply: (eutt_ret_steps tret); apply:eutt_sym H.
    * apply: cret.
  + exact/euttTau/eutt_trans/H0/H.
  + inversion t2imp as [|?? t'imp]; subst.
    case: (eutt_impure_steps t'imp (eutt_sym H)) =>
      k3 t3imp k21.
    apply: euttImpure.
    * apply/ts_tau/t3imp.
    * apply: cimp.
    * move=> x; exact/eutt_trans/Himp/eutt_sym/k21.
- case: (eutt_impure_steps t2k t2c) => k3 t3imp k23.
  apply: euttImpure.
  - exact: t1k.
  - exact: t3imp.
  - move=> x.
    exact: eutt_trans (k12 x) (k23 x).
Qed.

Lemma tau_steps_eutt_refl A (t1 t2 t : M A) :
  tau_steps t1 t -> tau_steps t2 t -> t1 ≊ t2.
Proof.
by move=> h h'; exact/tau_steps_euttL/tau_steps_euttR/eutt_refl/h'/h.
Qed.

CoFixpoint bindm_eutt A B (f : A -> M B) (d1 d2 : M A) :
    d1 ≊ d2 ->
    (d1 >>= f) ≊ (d2 >>= f).
Proof.
case=>[????++ r |*|*];
  [rewrite -r =>*
    | rewrite [X in X ≊ _]ITreeE [X in _ ≊ X]ITreeE /=; apply: euttTau
    | apply: euttImpure=>* ].
- by apply: tau_steps_eutt_refl; apply: tau_steps_bind_ret; eauto.
- exact: bindm_eutt.
- by apply: tau_steps_bind_impure; eauto.
- by apply: tau_steps_bind_impure; eauto.
- exact: bindm_eutt.
Qed.

CoFixpoint bindf_eutt A B (f g : A -> M B) (d : M A) :
    (forall a, (f a) ≊ (g a)) ->
    (d >>= f) ≊ (d >>= g).
Proof.
by case: d=> [[*|*|*]];
  rewrite ?bindretf //
    [X in X ≊ _]ITreeE [X in _ ≊ X]ITreeE /=;
    [apply: euttTau | apply: euttImpure=>* ];
    try exact: ts_refl;
    exact: bindf_eutt.
Qed.

#[export]
HB.instance Definition _ :=
  @hasWBisim.Build M (fun A => @eutt A A eq)
    eutt_refl eutt_sym eutt_trans (@bindm_eutt) (@bindf_eutt).

End itree_sec.
End ITreeWBisimModelM.

HB.about itree.
HB.about elgotMonad.
