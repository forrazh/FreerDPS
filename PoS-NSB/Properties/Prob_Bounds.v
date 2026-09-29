From mathcomp Require Import
  all_ssreflect ssralg poly ssrnum ssrint interval finmap
  mathcomp_extra boolp classical_sets functions cardinality fsbigop.

From mathcomp Require Import (canonicals) Rstruct.
From mathcomp Require Import
  reals ereal interval_inference topology normedtype sequences realfun
  convex real_interval derive esum measure exp numfun lebesgue_measure
  measurable_realfun lebesgue_integral kernel probability hoelder unstable
  archimedean.

Require Reals Interval.Tactic.
From HB Require Import structures.

From AUChain Require Import
  sampling Rstruct_topology Network Protocol GlobalState Blocks Messages
  MessageTuple Parameters BlockTree Schedule LocalState MemEq SsrFacts
  TreeChain CG CP CQ additional_lemmas.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import hoelder ess_sup_inf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Printing Notations.
Unset Printing Implicit.
Unset Printing Coercions.
Unset Printing Universes.
Unset Printing All.

Section PoSProbabilityBounds.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope schedule_scope.
(*Point sur SSreflect


SSreflect se base principalement sur la réecriture, et sur du forward Proving contrairement au Ltac

Les simplification se font de la manière suivante :

rewrite /=. : pour simplifier sans essayer de conclure

rewrite //=. : Pour simplifier et essayer de conclure (try easy globablement)

on utilise parfois by [] pour résoudre un but trivial.

L'introduction de variable se fait de la manière suivante :

move => a b.

On peut faire un destruct grace à move en faisant

move : H1 => [H2 H3]


Réecriture : 

rewrite theo : rewrite de la gauche vers la droite

rewrite -theo : rewrite de la droite vers la gauche


Fold et unfold :

rewrite /defintion : déplie la définition

rewrite -/definition : replie la définition



Alias : 

La notation :
set X := Y.
permet de définir un alias permettant de rendre les assertions et l'affichage dans l'assistant de preuve plus simple.


Assertions préliminaires (point important pour le forward proving) :

La notation :

have (nom de l'hypothèse) : (énoncé de l'hypothèse). {
    (preuve de l'hypothèse)
}

permet de prouver une sous hypothèse  à l'interieur d'une preuve , elle est notament important pour le forward proving
(on part de nos hypothèses et on les manipule pour tomber sur la conclusion).

Apply :

La notation :

apply : (lemme)

applique le théorème , elle est très semblable à celle du ltac mais il y a quelque nuances notament du ppint de vue du développeur.

la méthode apply de ssreflect éffectue l'application plus rapidement en terme de temps mais propage peu les raisons d'une erreur dans 
l'interface de preuve.

La méthode apply de ltac , elle propage quantité d'information de la raison de l'échec d'une application de lemme, mais pour des
raisons qui me sont inconnues, l'application est plus longue.

C'est pour cela que dans le code vous pourrez voir l'utilisation des deux tactiques elle sont adaptées suivant le temps d'éxecution
pour que le noyeau rocq valde la preuve, et le fait que j'ai eu besoin à un moment de voir le message d'erreur plus détaillé.

Views SSreflect :
SSreflect utilise souvent des "views" pour effectuer des conversions de type de proposition , on peut par exemple passer 
d'une forme booléene à une forme propositionnelle.

Tactiques utilisée : 

apply/eqP. : transforme le but d'égalité booléene en égalité propositionnelle.

apply/seteqP. : permet de montrer une égalité d'ensembles en montrant les deux inclusions.

move/negP in H. : transforme une négation booléene dans H en une hypothèses utilisable comme une négation propositionnelle.

case /andP : H => H1 H2. permet de destruct une conjonction booléene dans H en deux hypothèses H1 et H2.

apply/funext x : extensionnalité d'une fonction


cbv zeta déplie les (let in) locaux 

Congruence

congr (f _) : équivalent ssreflect de f_equal



Induction : 

elim n => [|n IHn].

pour faire une preuve par induction sur n et générer une hypothèse d'induciton 
*)




Let R := Rdefinitions.R.
Context {d} (T : measurableType d) (P : probability T R).

(* -------------------------------------------------------------------- *)
(* Shared probabilistic model                                            *)
(* -------------------------------------------------------------------- *)

Variable Sc : nat.
Hypothesis n_sup_O : (0 < Sc)%N.

Variable pLs pSs pAs : R.
Hypothesis pLs01 : (0 <= pLs <= 1)%R.
Hypothesis pSs01 : (0 <= pSs <= 1)%R.
Hypothesis pAs01 : (0 <= pAs <= 1)%R.

Variable LS : Sc.-tuple (bernoulliRV P pLs).
Variable SS : Sc.-tuple (bernoulliRV P pSs).
Variable AS : Sc.-tuple (bernoulliRV P pAs).

Definition LS_r := bool_trial_value LS.
Definition SS_r := bool_trial_value SS.
Definition AS_r := bool_trial_value AS.

Variable deltaLs deltaSs deltaAs : R.
Hypothesis delta_range_Ls : (0 < deltaLs < 1)%R.
Hypothesis delta_range_Ss : (0 < deltaSs < 1)%R.
Hypothesis delta_range_As : (0 < deltaAs < 1)%R.

(* -------------------------------------------------------------------- *)
(* Tuple utilities                                                       *)
(* -------------------------------------------------------------------- *)
(*fonction qui permet de récuperer un sous tuple de taille b - a , en gardant du tuple t passé en parametre,  b premiers éléments 
  et en retirant les a premiers éléments*)
Definition tuple_interval_index {T : Type} (a b n : nat) (t : n.-tuple T) :=
  drop a (take b t).


(*Preuve qu'on connait la taille d'un tuple t de taille n après en avoir retiré les b premiers éléments et en en retirant les a premiers,
  la taille est (b - a)

  Hypothèses : a < b et b <= n*)
Lemma tuple_interval_size {X : Type} (a b n : nat) (t : n.-tuple X) (Hab : (a<b)%N) (Hb : (b <= n)%N) :
  size (drop a (take b (tval t))) == (b-a)%N.
Proof.
  apply/eqP.
  rewrite size_drop size_take size_tuple.
  rewrite -/(minn b n).
  by rewrite (minn_idPl Hb).
Qed.

(*Fonction qui forme un tuple a partir de l'interval a b donné*)
Definition tuple_interval_index_fun ( a b n : nat) (t : n.-tuple T)
    (Hab : (a<b)%N) (Hb : (b <= n)%N) : ((b-a)%N).-tuple T :=
  Tuple (tuple_interval_size t Hab Hb).

Lemma Sc_pos_R : (0 < (Sc%:R : R))%R.
Proof.
  by rewrite ltr0n.
Qed.

(* -------------------------------------------------------------------- *)
(* Shared interval tuples                                               *)
(* -------------------------------------------------------------------- *)

(*Extrait du tuple LS les slots d'indices a à b - 1 et contruit un tuple de taille b - a*)
Definition LS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pLs) :=
  Tuple (tuple_interval_size LS Hab Hb).

(*Extrait du tuple SS les slots d'indices a à b - 1 et contruit un tuple de taille b - a*)
Definition SS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pSs) :=
  Tuple (tuple_interval_size SS Hab Hb).

(*Extrait du tuple AS les slots d'indices a à b - 1 et contruit un tuple de taille b - a*)
Definition AS_sub (a b : nat)
    (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
    (b - a).-tuple (bernoulliRV P pAs) :=
  Tuple (tuple_interval_size AS Hab Hb).

(* -------------------------------------------------------------------- *)
(* Shared Chernoff/complement bounds                                     *)
(* -------------------------------------------------------------------- *)

(*
Nous allons faire un point sur les notations et les éléments utilisés dans les suivants dans le fichier 

La notation let A := B in n'est qu'une notation qui permet de simplifier l'onglet de preuve de l'assisstant, elle 
effectue une simple substitution de texte qu'on peut introduire avec move => A.

On note X' comme fonction qui somme les variables aléatoires d'un tuple d'une réalisation donnée.

La notatation (\X_Sc P) construit la loi de Sc tirages indépendants chacun suivant la probabilité P, cette notation
est appliquée a des ensemble qui dans le monde des probabilités sont des événements, elle dénote grossierement la 
probabilité qu'un élément donné appartient à lensemble sur le quel cette probabilité est appliquée.

La notation 'E_(\X_Sc P)[X'] dénote l'ésperance probabiliste où (\X_Sc P) décrit les Sc tirages indépendants et [X']
décrit la fonction qui est utilisée pour sommer les variables aléatoires.

La notation en ensemble se fait de la sorte :
[set i | Prop]

Les ensembles peuvent être vus un peu comme des fonction qui renvoie True si le i qui est donné à cet ensemble appartient
bien à l'ensemble et False sinon.

Point important: si i n'apparait pas dans la propriété de séléction d'un ensemble , alors l'ensemble est détérministe et vaut donc
soit setT soit set0 et revoiera soit True pour tout i donné soit False pour tout i donné.

Les lemmes et théorèmes de mathcomp possèdent souvent des variables ayant des types spécifiques que rocq ne peut pas convertir automatiquement,
Il faut donc très souvent faire des conversions de types explicites ou bien spécifier le type que rocq n'arrive pas a inférer.

Pour faire une conversion de type on utilise la notation :  %:(TYPE VOULU)

Pour spécifier un type on utilise la notaiton : %(TYPE SPECIFIE)

Dans la majorité des preuves suivantes nous n'utiliserons globalement que les types suivants :

N : entier naturel 

R : réel

E : réel étendus (avec +infini et -infini)

Pour faire un Search il faut spécifiquement faire un Search en précisant le type.

Les opérateurs de comparaisons : < > <= >= sont aussi spécifiques par types il faut donc spécifier par exemple (a < b)%:R.

*)







(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme complémentaire de proba (1 - X) pour la borne sur les 
lucky slots*)
Lemma complementary_specialized_LS :
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i | ~~ (X' i <= (1 - deltaLs) * fine mu)%R ]%R
  =
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (\X_Sc P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
Proof.
  move => X' mu.
  by rewrite complementary_specialized_le.
Qed.

(*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous forme complémentaire*)
Lemma complementary_Ls_Bound :
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i | (1 - deltaLs) * fine mu <  X' i ]%R
  =
    let X' := bool_trial_value LS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E - (\X_Sc P) [set i | X' i <= (1 - deltaLs) * fine mu ]%R))%E.
Proof.
  move => X' mu.
  rewrite -complementary_specialized_LS .
  by rewrite set_gt_as_compl_le.
Qed.

(*borne inférieure exprimée sur le rapport elle est le résultat de transformations de la borne 
(sampling_ineq3 pLs01 LS delta_range_Ls).*)
Lemma complementary_LS_event :
  let X' := bool_trial_value LS in
  let mu := 'E_(\X_Sc P)[X'] in
  (((1%R)%:E - (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
  <=
  (\X_Sc P) [set i | (1 - deltaLs) * fine mu < X' i]%R)%E.
Proof.
  rewrite /=.
  have H1:= (sampling_ineq3 pLs01 LS delta_range_Ls).
  rewrite complementary_Ls_Bound /=.
  rewrite /= in H1.
  set X' := bool_trial_value LS.
  set mu := 'E_(\X_Sc P)[X'].
  rewrite /mu -leeN2 in H1.
  rewrite /mu.
  by apply : leeD2l H1.
Qed.

(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme complémentaire de proba (1 - X) pour la borne sur les 
super slots*)
Lemma complementary_specialized_SS :
  let X' := bool_trial_value SS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i | ~~ (X' i <= (1 - deltaSs) * fine mu)%R ]%R
  =
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (\X_Sc P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
Proof.
  move => X' mu.
  by rewrite complementary_specialized_le.
Qed.

(*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous forme complémentaire*)
Lemma complementary_SS_bound:
  let X' := bool_trial_value SS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i | (1 - deltaSs) * fine mu <  X' i ]%R
  =
    let X' := bool_trial_value SS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (\X_Sc P) [set i | X' i <= (1 - deltaSs) * fine mu ]%R))%E.
Proof.
  move => X' mu.
  rewrite -complementary_specialized_SS.
  by rewrite -(set_gt_as_compl_le).
Qed.

(*borne inférieure exprimée sur le rapport elle est le résultat de transformations de la borne 
(sampling_ineq3 pSs01 SS delta_range_Ss).*)
Theorem complementary_SS_event :
  let X' := bool_trial_value SS in
  let mu := 'E_(\X_Sc P)[X'] in
  (((1%R)%:E -
    (expR (-(fine mu * deltaSs ^+ 2) / 2)%R)%:E)%E
  <=
  (\X_Sc P)
    [set i | (1 - deltaSs) * fine mu < X' i]%R)%E.
Proof.
  rewrite /=.

  have H1:= (sampling_ineq3 pSs01 SS delta_range_Ss).
  rewrite complementary_SS_bound /=.
  rewrite /= in H1.
  set X' := bool_trial_value SS.
  set mu := 'E_(\X_Sc P)[X'].
  rewrite /mu -leeN2 in H1.
  rewrite /mu.
  by apply : leeD2l H1.
Qed.



(*Lemme qui fait sortir la négation de la condition de l'ensemble en une forme complémentaire de proba (1 - X) pour la borne sur les 
adversarial slots*)
Lemma complementary_specialized_AS :
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i | ~~ (X' i >= (1 + deltaAs) * fine mu)%R ]%R
  =
    let X' := bool_trial_value AS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (\X_Sc P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
Proof.
  rewrite /= .
  set X' := bool_trial_value AS.
  set mu := 'E_(\X_Sc P)[X'].
  set B :=  (1 + deltaAs) * fine mu.
  set A := [set i | X' i >= B ].
  set Pr := (\X_Sc P).
  have  Hsame :
    [set i | ~~ (X' i >= B )] = ~` A.
  {
    apply/seteqP.
    split.
    - move => i Hi.
      rewrite /A /= .
      rewrite /= in Hi.
      move /negP in Hi.
      apply Hi.
    move => i Hi.
    rewrite /A /= in Hi.
    rewrite /=.
    apply /negP.
    apply Hi.
  }
  rewrite Hsame.
  apply probability_setC.
  rewrite -(ST_Set A).
  apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g :=X' )) .
  - apply: measurableT.
  - by rewrite //=.
  by rewrite //=.
Qed.

(*Changment de sens de l'inégalité dans l'événement en écrivant l'ensemble sous forme complémentaire*)
Lemma complementary_AS_bound:
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_Sc P)[X'] in
  (\X_Sc P) [set i |  X' i   < (1 + deltaAs) * fine mu ]%R
  =
    let X' := bool_trial_value AS in
    let mu := 'E_(\X_Sc P)[X'] in
    (((1%R)%:E -
      (\X_Sc P) [set i | X' i >= (1 + deltaAs) * fine mu ]%R))%E.
Proof.
  rewrite -complementary_specialized_AS /=.
  set X' := bool_trial_value AS.
  set mu := 'E_(\X_Sc P)[X'].
  set B := ((1 + deltaAs) * fine mu)%R.
  have Hset :
    [set i | X' i  < B]%R =
    [set i | ~~ (X' i >= B)%R].
  {
    rewrite seteqP.
    split.
    - move  => i Hn /=.
      rewrite -ltNge.
      apply Hn.
    move => i Hn /=.
    rewrite /= -ltNge in Hn.
    apply Hn.
  }
  by rewrite Hset.
Qed.
(*borne inférieure exprimée sur le rapport elle est le résultat de transformations de la borne 
(sampling_ineq2 pAs01 AS n_sup_O delta_range_As).*)
Theorem complementary_AS_event :
  let X' := bool_trial_value AS in
  let mu := 'E_(\X_Sc P)[X'] in
  (((1%R)%:E -
    (expR (-(fine mu * deltaAs ^+ 2) / 3)%R)%:E)%E
  <=
  (\X_Sc P)
    [set i | X' i < (1 + deltaAs) * fine mu]%R)%E.
Proof.
  rewrite /=.

  have H1:= (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
  rewrite complementary_AS_bound /=.
  rewrite /= in H1.
  set X' := bool_trial_value AS.
  set mu := 'E_(\X_Sc P)[X'].
  rewrite /mu -leeN2 in H1.
  rewrite /mu.
  by apply : leeD2l H1.
Qed.

(* ==================================================================== *)
(* Chain Growth                                                         *)
(* ==================================================================== *)

    Section ChainGrowth.

      (* Protocol assumptions specific to Chain Growth. *)

      (*GlobalStates assumptions*)
      Variables (N_from_r N'_from_r : Sc.-tuple T -> GlobalState).
      Hypothesis N_from_initial : forall r, N0 ⇓ N_from_r r .
      Hypothesis N_is_ready : forall r, N_from_r r @ Ready.
      Hypothesis N'_from_N :  forall r, N_from_r r  ⇓^+ N'_from_r r.

      Search "measurable_fun_le".


      (*party assumptions corresponding to CG assumptions for now*)
      Variables (p1 p2 : Party).
      Hypothesis p1_honest : is_honest p1.
      Hypothesis p2_honest : is_honest p2.

      (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
      Variable (l1_from_r l2_from_r : Sc.-tuple T -> LocalState).
      Hypothesis l1_p1_state : forall r, has_state p1 (N_from_r r) (l1_from_r r).
      Hypothesis l2_p2_state : forall r, has_state p2 (N'_from_r r)  (l2_from_r r).

      (*Assumption to link the bool_trial_value LS to the amount of lucky slots between N and N'*)
      Hypothesis LS_r_eq_slotrange : forall r, (LS_r r  = | lucky_slots_range (t_now (N_from_r r)) ((t_now (N'_from_r r)) - 1) |%:R)%N.

      Definition Chain_growth_ls_Good_event :=
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        [set r | ((1 - deltaLs) * fine mu < X' r)%R].

      Definition chain_growth_parties_event (w : nat)  :=
        [set r : Sc.-tuple T |
          ((|bestChain (t_now (N_from_r r) - 1)%N (tree (l1_from_r r))| + w)%N
            <= |bestChain (t_now (N'_from_r r) - 1)%N (tree (l2_from_r r))|)%N].

      (*if you want to make a chain growth event that takes in condiseration a given r, you are in the obligation
      to define functions on Global state and LocalState that depends on a given r, those functions are abstract
      , meaning that no mater what we won't be apple to prove they are measurable*)
      Hypothesis chain_growth_parties_event_measurable :
        forall w : nat,
          measurable (chain_growth_parties_event w).
      

      (*Lemme qui montre que pour tout r si w%:r <= (1 - deltals) * fine mu  alors l'événement probabiliste implique l'événement du protocole*)
      Lemma Good_Ls_implies_chain_growth w :
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        w%:R <= (1 - deltaLs) * fine mu ->
        (forall r, Chain_growth_ls_Good_event r -> chain_growth_parties_event w r).
      Proof.
        move => X' mu H1 r H2.
        rewrite /chain_growth_parties_event //=.
        (*application du théorème chain growth du fichier CG.v , la plupart des hypothèses non probabilistes son triviales et donc résolues par easy
        il ne reste plus que w <= |lucky_slots_range (t_now N) (t_now N' - 1)| à démontrer*)
        apply chain_growth_parties with (p1 := p1) (p2 := p2) ; try easy.
        (*dépliage de la défintion de l'événement probabiliste*)
        rewrite /Chain_growth_ls_Good_event in H2.
        (*transformation de l'inégalité entre naturels en une inégalité de réels*)
        rewrite -(ler_nat R).
        (*utilisation de l'hypothèse de lien entre la quantité de lucky slot du modèle probabiliste et la quantité présente
        dans le protocole*)
        rewrite -(LS_r_eq_slotrange r).
        (*a < b -> a <= b*)
        apply ltW in H2.
        (*on applique la transitivité avec H1
          pour qu'a partir du goal
          w%:R <= LS_r r
          et de l'hypothèse w%:R <= (1 - deltaLs) * fine mu
          on ait à démontrer que (1 - deltaLs) * fine mu <= LS_r r qui est notre hypothèse H2
        *)
        apply (le_trans H1).
        apply H2.
      Qed.
      

      (*Lemme qui utilise l'implication des événement pour démontrerque l'événement a une probabiltié supérieure
        On utilise la formule avec le lemme précédent : (A -> B) -> Pr[A] <= Pr[B] avec A et B deux événements.
      *)
      Lemma probability_implication (w : nat) :
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        w%:R <= (1 - deltaLs) * fine mu ->
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        ((\X_Sc P) Chain_growth_ls_Good_event
          <= (\X_Sc P) (chain_growth_parties_event w))%E .
      Proof.
        move => X' mu H1.
        (*renomage de variable pour rendre les énoncés d'assert plus cours et plus compréhensibles*)
        set B := ((1 - deltaLs) * fine mu)%R.
        (*permet de démontrer que si on a deux événement A et B mesurables avec A -> B alors (\X_x P) B >= (\X_x P) A.
         Ici le théorème est appliqué a [Chain_growth_ls_Good_event] et a [chain_growth_parties_event w]
         on va ainsi démontrer que les deux événement sont mesurables et que 
         [Chain_growth_ls_Good_event] -> [chain_growth_parties_event w]

        *)
        apply: le_measure.
        - (*mesurabilité de Chain_growth_ls_Good_event *)
          rewrite /Chain_growth_ls_Good_event -/X'.
          rewrite -/B.
          (*On dispose dans math comp uniquement d'un théorème permettant de démontrer que
        si on  a SetT `&` [set r | f(x) <= g(x)] , ici nous somme dans le cas où nous avons
        inégalité stricte entre les B et X' r. L'objectif dans un premier temps est d'exprimer
        l'inégalité stricte en son complémentaire (inférieur ou égal). Pour cela on utilise
        un lemme de additional_lemmas.v démontrant 
        que [set r  | (B < X r)%R] = ~` [set r | (X r <= B)%R]*)   
          rewrite set_lt_eq_neg_le.

          have Hle :
            (measurable_structure.measure_tuple_display d).-measurable [set r | (X' r <= B)%R] .
          {
            (*on fait apparaitre l'intersection entre SetT et notre intervale*)
            rewrite -(ST_Set [set r | X' r <= B]).
            (*On peut désormais appliquer le lemme qui montre que SetT `&` [set r | f(x) <= g(x)]*)
            apply (measurable_fun_le (D := setT) (f := X') (g := fun _ => B)); rewrite //=.
          }
          rewrite //=.
          rewrite inE.
          (*on a exprimé l'ensembe en son complémentaire ,
        on peut donc avec le lemme measurableC montrer 
        que le complémentaire de l'enseble est lui aussi mesurable*)
          apply : measurableC.
          apply Hle.

        (*On montre que chain chain_growth_parties_event est mesurable a partir de l'hypothèse
         que l'événement est mesurable*)
        - rewrite /chain_growth_parties_event.
          rewrite  //=.
          rewrite inE.
          apply chain_growth_parties_event_measurable.

        move =>r.
        (*On applique notre lemme pour montrer l'implication entre les deux événements
      ce qui implique l'inégalité qu'on veut prouver sur les probabilités de ces événements*) 
        apply Good_Ls_implies_chain_growth.
        apply H1.
      Qed.


      (*A partir des Lemmes précédents on montre par transitivité une borne sur 
        Chain Growth*)
      Theorem Chernoff_bound_chain_growth_parties_even (w:nat):
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        w%:R <= (1 - deltaLs) * fine mu ->
        let X' := bool_trial_value LS in
        let mu := 'E_(\X_Sc P)[X'] in
        (
          ((1%R)%:E - (expR (-(fine mu * deltaLs ^+ 2) / 2)%R)%:E)%E
          <=
          ((\X_Sc P) (chain_growth_parties_event w))%E
        )%E.
      Proof.
        move => X' mu H.
        apply (le_trans complementary_LS_event).
        apply (probability_implication  H).
      Qed.

    End ChainGrowth.

(* ==================================================================== *)
(* Chain Quality                                                        *)
(* ==================================================================== *)

    Section ChainQuality.

      Variable (N : GlobalState).
      Hypothesis N_from_initial : N0 ⇓ N.
      Hypothesis N_forging_free : forging_free N.
      Hypothesis N_collision_free : collision_free N.

      Variable (p : Party).
      Hypothesis p_is_honest : is_honest p.

      Variable (l : LocalState).

      Hypothesis p_has_state_l: has_state p N l.

      Variable (b_i b_j : Block).
      Variable (c : Chain).
      Hypothesis interval_is_fragment_of_best :
        fragment ([:: b_j] ++ c ++ [:: b_i]) (bestChain ((t_now N)-1)%N (tree l)).

      Variable (w_cq : nat) (r_cq : Sc.-tuple T).
      Variable (ds : nat).
      
      (*assumption that ds is of size slot of B_j - slot of B_i*)
      Hypothesis ds_eq_fragment_size : ds = (sl b_j - (sl b_i + 1))%N.

      (*hypothèse de lien entre le modèle probabiliste et le modèle du protocole sur le fait qu'on ait  un comptage équivalent         
        de lucky slots et adversarial slots sur un intervalle [a, b) avec a < b et b <= Sc, dans le protocole et le modèle probabiliste*)
      Hypothesis Ls_r_range_link :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          bool_trial_value (LS_sub Hab Hb)
            (tuple_interval_index_fun r_cq Hab Hb)
          = | lucky_slots_range a b |%:R.

      Hypothesis As_r_range_link :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          bool_trial_value (AS_sub Hab Hb)
            (tuple_interval_index_fun r_cq Hab Hb)
          = | adv_slots_range a b |%:R.

      

      (*Hypotheses qui sera à recréer de manière implicite à partir de la condition sur la lottery(il existe epsilon tel que : pLs >= pAs + epsilon)
        elle dit globalement que pour tout sous intervalle de taille plus grande que ds d'un tuple de base de taille Sc, On a a partir de 
         deltaAs deltaLs et pAs pLs qu'on a une domination de l'eperence sur cet intervalle d'au moins w_cq.
        *)
      Hypothesis w_cq_bound :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          (ds <= b - a)%N ->
          ((1 + deltaAs) * fine 'E_(\X_(b-a) P)[bool_trial_value (AS_sub Hab Hb)] + w_cq%:R
            <=
            (1 - deltaLs) * fine 'E_(\X_(b-a) P)[bool_trial_value (LS_sub Hab Hb)])%R.
      (*hypothèse a probablement supprimer*)
      Hypotheses w_cq_gt_0 : (w_cq > 0)%N.

      (*there is enough lucky slots*)
      Definition LS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
        let X' := bool_trial_value (LS_sub Hab Hb) in
        let muLS := 'E_(\X_(b-a)%N P)[X'] in
        [set r | (1 - deltaLs) * fine muLS < X' r].

      (* there is a satisfying number of adversarial slots*)
      Definition AS_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
        let X' := bool_trial_value (AS_sub Hab Hb) in
        let muAS := 'E_(\X_(b-a)%N P)[X'] in
        [set r | (1 + deltaAs) * fine muAS > X' r].
      (*conjonction entre les deux intervalles probabilistes sur les lucky slots et les adversarial slots sur un intervalle [a,b)*)
      Definition CQ_good_event (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :=
        (LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ  Hab Hb).

      (*          
         événement probabiliste CQ_good_event replongé dans l'espace probabiliste des Sc slots.
         L'événement est défini de la sorte (match with) pour offir des preuves plus simples dans les preuves
         ultérieures

          Grace à ce type de définition on peut ainsi définir un événement qui contient un forall implicite
         Sans cette forme on définirait cet événement comme étant
         [set r | forall  a b (Hab : a < b)%N (Hb : b <= Sc) CQ_good_event Hab Hb (tuple_interval_index_fun r Hab Hb)]
         
      *) 
      Definition CQ_interval_good_event (a b : nat) : set (Sc.-tuple T) :=
        match boolP (a < b)%N with
        | AltTrue Hab =>
            match boolP (b <= Sc)%N  with
            | AltTrue Hb =>
                [set r : Sc.-tuple T | CQ_good_event Hab Hb (tuple_interval_index_fun r Hab Hb)]
            | _ => setT
            end
        | _ => setT
        end.

      (*événement qui définit que pour tout intervalle [a,b[ avec a < b et b <= Sc
        et d <= b - a, on a un avantage d'au moins w lucky slots sur les adversarial lucky_slots_range

         C'est l'événement qui représente la partie protocole de la modélisation, si cet événement est 
         reussi alors, on peut appliquer chain chain_quality
      *)
      Definition CQ_slot_advantage (w d : nat) : Prop :=
        forall (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N),
          (d <= b - a)%N ->
          ((| adv_slots_range  a b| + w) <= | lucky_slots_range a b |)%N.

      (* Lemme qui verifie que pour a et b donnés qui verifient a < b , b <= Sc et ds <= b - a,
         on a que notre événement probabiliste sur l'intervalle [a,b[ de l'execution fixe r_cq
         implique qu'on a un avantage de au moins w_cq lucky slots sur les adversarial slots

         Cet événement fait directement rapport avec la preuve mathématique de chain quality
         dans la première partie où on travaille d'abord sur un intervalle donné [a,b[

      *)
      Lemma CQ_good_interval_implies_advantage (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) (Hsize : (ds <= b - a)%N) :
        CQ_good_event Hab Hb (@tuple_interval_index_fun a b Sc r_cq Hab Hb)
        -> ((| adv_slots_range  a b| + w_cq) <= | lucky_slots_range a b |)%N.
      Proof.
        move => HGE.
        (*On déplie les définitions et on réecrit nos hypothèses sur le lien entre le modèle probabiliste et le protocole*)
        rewrite /CQ_good_event /LS_good_event_CQ /AS_good_event_CQ in HGE .
        rewrite /= As_r_range_link Ls_r_range_link in HGE.
        (*on a une conjonction de l'expression dépliée de LS_good_event_CQ et de l'expression dépliée de AS_good_event_CQ
          , on introduit deux nouvelles hypothèses qui sont chacune un élément de la conjonction*) 
        move : HGE => [HLS HAS].

        (*on instancie l'hypothèse sur la borne w_cq spécialisée sur notre intervalle [a,b[ *)
        have Hw := w_cq_bound Hab Hb Hsize.
        (*transformation de l'inégalité entre entiers naturels en une inégalités de réels*)
        rewrite -(ler_nat R) natrD.

        rewrite //= in Hw.

        (*définitions et application d'alias pour simplifier l'affichage*)
        set muAS := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool (AS_sub Hab Hb)) i)].
        set muLS := fine 'E_(\X_(b - a) P)[(\sum_(i < b - a) Tnth (real_of_bool (LS_sub Hab Hb)) i)].
        rewrite -/muAS -/muLS in Hw.
        rewrite -/muAS in HAS.
        rewrite -/muLS in HLS.

        (* On a (1 + deltaAs) * muAS + w_cq%:R <= (1 - deltaLs) * muLS
             et 
             (1 - deltaLs) * muLS < (| lucky_slots_range a b |)%:R
            
             donc par transitivité on a aussi
             (1 + deltaAs) * muAS + w_cq%:R <  (| lucky_slots_range a b |)%:R
          *) 
        have Htrans1 := le_lt_trans Hw HLS.

        have HASw : (| adv_slots_range a b |)%:R + w_cq%:R < (1 + deltaAs) * muAS + w_cq%:R.
        {
          (*on a (1 - deltaLs) * muLS < (| lucky_slots_range a b |)%:R donc
              en additionnant w_cq des deux cotés on a aussi 
              HASW*) 
          by rewrite ltrD2r.
        }

        (*application de la transitivité entre HASw Htrans1 qui nous permet de conclure
            en changeant l'inégalité stricte en une ingégalité large de*)
        have htrans3 := lt_trans HASw Htrans1.

        by apply ltW in htrans3.
      Qed.

      (*if for every sub interval of size at least static variable ds of the static interval r_cq,
        we have that forall interval [a b] where the interval is ge than the fixed variable ds that
        the number of lucky slot is greater than the fixed  variable w_cq *)
      Lemma CQ_all_interval_good_implies_advantage :
        (forall a b, CQ_interval_good_event a b r_cq) -> CQ_slot_advantage w_cq ds.
      Proof.
        move => HAIG.
        rewrite /CQ_slot_advantage.
        move => a0 b0 Hab Hb Hds.
        rewrite /CQ_interval_good_event in HAIG.
        specialize (HAIG a0 b0).
        destruct (boolP (a0 < b0)%N) as [Hab' | Hnab'].
        - destruct (boolP (b0 <= Sc)%N) as [Hb' | Hnb'].
          + destruct (boolP (ds <= b0 - a0)%N) as [Hds' | Hnds'].
            * rewrite /= in HAIG.
              have Habs : Hab = Hab'.
              {
                rewrite //=.
              }
              have Hbs : Hb = Hb'.
              {
                rewrite //=.
              }
              apply (@CQ_good_interval_implies_advantage a0 b0 Hab Hb Hds).
              by rewrite Habs Hbs.
            * by rewrite /negb Hds in Hnds'.
          + by rewrite /negb Hb in Hnb'.
        - by rewrite /negb Hab in Hnab'.
      Qed.
      

      (*preuve de la mesurailité de la fonction qui extrait les sous tuples, en démontrant que les projections du sous tuple sur le tuple initial
         son mesurables (globalement on démontre que l'indice d'un élément dans le tuple initial d'un a + m avec m l'indice de l'élément dans le 
         tuple obtenu)*)
      Lemma measurable_tuple_interval_index_fun
          (a b : nat)
          (Hab : (a < b)%N)
          (Hb : (b <= Sc)%N) :
        measurable_fun [set: Sc.-tuple T]
          (fun r : Sc.-tuple T =>
            tuple_interval_index_fun r Hab Hb).
      Proof.
        apply/measurable_fun_tnthP => i.
        destruct i.
        have ty : (a + m < b)%N. {
          Check ltn_subRL.
          by rewrite -ltn_subRL.
        }
        have HSc_ai := ltn_leq_trans ty Hb.
        rewrite /comp /=.
        pose j : 'I_Sc := @Ordinal Sc (a + m) HSc_ai.
        rewrite /tuple_interval_index_fun /=.
        have Hcoord (x : Sc.-tuple T) :
          tnth (Tuple (tuple_interval_size x Hab Hb)) (Ordinal i)
          =
          tnth x j.
        {
          rewrite [LHS](tnth_nth (tnth x j)) /=.
          rewrite nth_drop.
          rewrite nth_take.
          change (nth (tnth x j) (tval x) (val j) = tnth x j).
          exact: esym (tnth_nth (tnth x j) x j).
          exact : ty.
        }
        have Hfun :
            (fun x : Sc.-tuple T =>
              tnth (Tuple (tuple_interval_size x Hab Hb)) (Ordinal i))
            =
            (fun x : Sc.-tuple T => tnth x j).
        {
          apply/funext => x.
          exact: Hcoord x.
        }
        rewrite Hfun.
        exact: measurable_tnth.
      Qed.
      

      (*preuve de mesurabilité du bon événement probabiliste sur les lucky slots sur un intervale [a,b)*)
      Lemma LS_measurable_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :
        measurable (LS_good_event_CQ Hab Hb).
      Proof.
        rewrite /LS_good_event_CQ.
        set X' := bool_trial_value (LS_sub Hab Hb).
        set muLS := 'E_(\X_(b - a) P)[X'].
        set B := (1 - deltaLs) * fine muLS.
        rewrite set_lt_eq_neg_le.
        apply : measurableC.
        rewrite -(ST_Set [set r |  X' r <= B]).
        apply: (measurable_fun_le (D := setT) (f := X' ) (g := fun _ => B)).
        - apply : measurableT.
        - rewrite //=.
        rewrite //=.
      Qed.

      (*preuve de mesurabilité du bon événement probabiliste sur les adversarial slots sur un intervale [a,b)*)
      Lemma AS_measurable_good_event_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
        measurable (AS_good_event_CQ Hab Hb).
      Proof.
        rewrite /AS_good_event_CQ.
        set X' := bool_trial_value (AS_sub Hab Hb).
        set muAS := 'E_(\X_(b - a) P)[X'].
        set B := (1 + deltaAs) * fine muAS.
        have Hcomp :
          [set r | X' r < B] = [set r | ~~ (B <= X' r)].
        {
          apply /seteqP.
          split.
          - move => r //= Hr ; by rewrite -ltNge.
          move => r //= Hr. by rewrite -ltNge in Hr.
        }
        rewrite Hcomp.
        have HsetNcomp :
          [set r | ~~ (B <= X' r)] = ~` [set r | B <= X' r].
        {
          apply /seteqP.
          split.
          - move => r Hr.
            rewrite //=.
            rewrite //= in Hr.
            move /negP in Hr.
            apply : Hr.
          - move => r Hr.
            rewrite //=.
            rewrite //= in Hr.
            move /negP in Hr.
            apply Hr.
        }

        rewrite  HsetNcomp.
        apply measurableC.
        rewrite -(ST_Set ([set r | B <= X' r])).
        apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := X')).
        - by apply: measurableT.
        - rewrite  //=.
        rewrite //=.
      Qed.
      

      (*preuve de mesurabilité sur le bon événement gloabal de chain quality sur un intervale [a,b) (conjonction du bon événement sur lucky et adversarial slots)*)
      Lemma CQ_good_event_measurable (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
        measurable (CQ_good_event Hab Hb).
      Proof.
        apply measurableI.
        - apply LS_measurable_good_event_CQ.
        apply AS_measurable_good_event_CQ.
      Qed.

      Variable (epsilon : R).
      

      (*preuve pour l'instant inutile mais à potentiellement exploiter plus tard, dit que si l'esperance de LS est strictement plus
      grande que l'esperance de AS, alors pour tout r si la valeure calculée du modèe probabiliste sur la réalisation r est plus grande que
      son esperance pour les deux types de slots , alors on a un avantage de la valeure calculée du modèle probabiliste des lucky slots sur 
      les adversarial slots*)
      Lemma LS_gt_AS (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
        let XLS := bool_trial_value (LS_sub Hab Hb) in
        let XAS := bool_trial_value (AS_sub Hab Hb) in
        let muLS := 'E_(\X_(b-a) P)[XLS] in
        let muAS := 'E_(\X_(b-a) P)[XAS] in
        (1+deltaAs) * fine muAS < (1 - deltaLs) * fine muLS ->
        forall r,
          (1+deltaAs) * fine muAS > AS_r r ->
          ((1-deltaLs) * fine muLS) < LS_r r ->
          (LS_r r > AS_r r).
      Proof.
        cbv zeta.
        move => H r HAS HLS.
        apply: (lt_trans HAS).
        apply: (lt_trans H).
        apply HLS.
      Qed.
      

      (*Lemme qui permet d'isoler epsilon dans la partie gauche de l'inéquation depuis la première inéquation*)
      Lemma epsilon_condition_CQ :
        (1 - deltaLs) * (pAs + epsilon) >
        (1 + deltaAs) * pAs <->
        epsilon > (((1 + deltaAs) / (1 - deltaLs)) - 1) * pAs.
      Proof.
        split.
        - move => H.
          rewrite (mulrC (1 - deltaLs) (pAs + epsilon) ) in H.
          rewrite -(ltr_pdivrMr (pAs + epsilon)) in H.
          rewrite (mulrC (1 + deltaAs)) in H.
          rewrite (mulrC pAs) in H.
          rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaLs)^-1))  mulrA.
          apply : H.
          rewrite subr_gt0.
          move/andP : delta_range_Ls => [H1 H2].
          apply H2.
        move => H.
        rewrite (mulrC (1 - deltaLs) (pAs + epsilon) ).
        rewrite -(ltr_pdivrMr (pAs + epsilon)) .
        rewrite (mulrC (1 + deltaAs)).
        rewrite (mulrC pAs).
        rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaLs)^-1))  mulrA in H.
        apply : H.
        rewrite subr_gt0.
        move/andP : delta_range_Ls => [H1 H2].
        apply H2.
      Qed.


      (*Lemme qui permet d'exprimer l'intersection entre LS_good_event_CQ et AS_good_event_CQ
        en une forme "complémentaire", en exprimant l'intersection comme 1 - [probabilité qu'un des deux événements échoue]
      *)
      Lemma union_bound_LS_AS_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
        (\X_(b-a) P) ((LS_good_event_CQ Hab Hb) `&` (AS_good_event_CQ Hab Hb))
        =
        (1%R%:E - (\X_(b-a) P) ((~` (LS_good_event_CQ Hab Hb)) `|` (~` (AS_good_event_CQ Hab Hb))))%E.
      Proof.
        rewrite -probability_setC.
        - congr ((\X_(b-a) P) _).
          apply /seteqP.
          split.
          + move => r [Hl Hr].
            move => [Hll | Hrr].
            + rewrite //=.
            rewrite //=.
          + move => r H.
            split.
            * apply : Classical_Prop.NNPP => HLS.
              apply : H.
              by left.
            apply : Classical_Prop.NNPP => HAS.
            apply : H.
            by right.
        - apply : measurableU.
          + apply measurableC.
            apply LS_measurable_good_event_CQ.
          apply measurableC.
          apply AS_measurable_good_event_CQ.
      Qed.

      
      (*Lemme qui applique l'inégalité de boole (union bound) à l'union des mauvais événement probabilistes pour pouvoir la borner par une somme*)
      Lemma bad_event_union_bound_CQ (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :
        ((\X_(b - a)%N P) ((~` LS_good_event_CQ Hab Hb) `|` (~` AS_good_event_CQ Hab Hb))%E
        <=
        ((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) + ((\X_(b - a)%N P) (~` AS_good_event_CQ Hab Hb)))%E.
      Proof.
        apply : measureU2 ; apply : measurableC.
        - apply : LS_measurable_good_event_CQ.
        apply : AS_measurable_good_event_CQ.
      Qed.
      

      (*Borne supérieure de la somme des probabilités des mauvais événements probabilistes, en utilisant les inéquations de concentration*)
      Lemma bad_event_chernoff_bound (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N) :
        let XLS' := bool_trial_value (LS_sub Hab Hb)  in
        let muLS := 'E_(\X_(b-a)%N P)[XLS'] in
        let XAS' := bool_trial_value (AS_sub Hab Hb) in
        let muAS := 'E_(\X_(b-a)%N P)[XAS'] in
        (((\X_(b - a)%N P) (~` LS_good_event_CQ Hab Hb)) +
         ((\X_(b - a)%N P) (~` AS_good_event_CQ Hab Hb))
        <=
        (((expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E) +
         ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E)%E.
      Proof.
        cbv zeta.
        set XLS' := (bool_trial_value (LS_sub Hab Hb)).
        set muLS := 'E_(\X_(b-a)%N P)[XLS'].
        set XAS' := (bool_trial_value (AS_sub Hab Hb)).
        set muAS := 'E_(\X_(b-a)%N P)[XAS'].

        have HLS :
          (((\X_(b - a) P) (~` LS_good_event_CQ Hab Hb))%E
          <=
          (expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E)%E.
        {
          rewrite /LS_good_event_CQ.
          rewrite -try3.
          apply  (sampling_ineq3 pLs01 (LS_sub Hab Hb) delta_range_Ls).
        }
        have HAS :
          (((\X_(b - a) P) (~` AS_good_event_CQ Hab Hb))%E
          <=
          (expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E)%E.
        {
          rewrite /AS_good_event_CQ.
          rewrite -try2.
          have Hab' : (a < b)%N. {
            easy.
          }
          apply ltn_sub2r with (p := a) in Hab'.
          rewrite subnn in Hab'.
          rewrite /muAS.
          rewrite /XAS'.
          apply  (sampling_ineq2 pAs01 (AS_sub Hab Hb) Hab' delta_range_As).
          apply Hab'.
        }

        apply (leeD HLS HAS).
      Qed.
      

      (*Borne inférieure sur la probabilté que le bon événement probabiliste de Chain quality (bon événement probabiliste sur les lucky et adversarial slots)
        soit réussi sur l'invervalle [a,b) en utilsant encore une fois les borne de concentration*)
      Theorem CQ_good_event_lower_bound (a b : nat) (Hab : (a<b)%N) (Hb : (b <= Sc)%N):
        let XLS' := bool_trial_value (LS_sub Hab Hb)  in
        let muLS := 'E_(\X_(b-a)%N P)[XLS'] in
        let XAS' := bool_trial_value (AS_sub Hab Hb) in
        let muAS := 'E_(\X_(b-a)%N P)[XAS'] in
        ((1%R%:E -
        ((expR (-(fine muLS * deltaLs ^+ 2) / 2)%R)%:E) -
        ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E
        <=
        (\X_(b-a)%N P) (CQ_good_event Hab Hb))%E.
      Proof.
        rewrite union_bound_LS_AS_CQ.
        set U := (\X_(b-a)%N P) (~` LS_good_event_CQ Hab Hb `|` ~` AS_good_event_CQ Hab Hb).
        cbv zeta.
        rewrite -addeA.
        rewrite leeD2l.
        - by [].
        rewrite /U.
        rewrite -oppeD.
        - rewrite leeN2.
          apply (le_trans (bad_event_union_bound_CQ Hab Hb)).
          rewrite leeD.
          + by [].
          rewrite /LS_good_event_CQ.
          apply: (le_trans _ (sampling_ineq3 pLs01 (LS_sub Hab Hb) delta_range_Ls)).
          apply : le_measure.
          * rewrite inE.
            rewrite -try3.
            rewrite -(ST_Set ([set r | bool_trial_value (LS_sub Hab Hb) r <= (1 - deltaLs) * fine 'E_(\X_(b-a)%N P)[(bool_trial_value (LS_sub Hab Hb)) ] ] ) ).
            apply: (measurable_fun_le (D := setT)).
            -- apply : measurableT.
            -- rewrite //=.
            rewrite //=.
          * rewrite inE.
            rewrite -(ST_Set ([set i | bool_trial_value (LS_sub Hab Hb) i <= (1 - deltaLs) * fine 'E_(\X_(b-a)%N P)[(bool_trial_value (LS_sub Hab Hb))] ] ) ).
            apply: (measurable_fun_le (D := setT)).
            -- apply : measurableT.
            -- rewrite //=.
            rewrite //=.
          move => r Hr.
          rewrite -try3 in Hr.
          exact: Hr.
        rewrite /AS_good_event_CQ.
        rewrite -try2.
        have Haltb : (a < b)%N.
        {
          apply Hab.
        }
        have H0ltab : (0 < b - a)%N.
        {
          apply ltn_sub2r with (p:=a) in Haltb.
          rewrite subnn in Haltb.
          apply Haltb.
          apply Hab.
        }
        apply (sampling_ineq2 pAs01 (AS_sub Hab Hb) H0ltab delta_range_As).
        rewrite //=.
      Qed.


      (*the event thatthere is probabilisticly enough lucky slot and less adversarial slots is measurable for every subinterval [a,b] where d >= a b*)
      Lemma measurable_interval_good :
        forall a b , measurable (CQ_interval_good_event  a b).
      Proof.
        move => a b.
        rewrite /CQ_interval_good_event.
        destruct (boolP (a < b)%N) as [Hab' | Hnab'].
        - destruct (boolP (b <= Sc)%N) as [Hb' | Hnb'].
          + Search "measurable" .
            Search (measurable [set _ | ?D ?i]).
            have Hfun := measurable_tuple_interval_index_fun Hab' Hb'.
            have Hgood_event := CQ_good_event_measurable Hab' Hb'.
            have Hpre := Hfun measurableT (CQ_good_event Hab' Hb') Hgood_event.
            rewrite setTI  in Hpre.
            apply Hpre.
          + exact : measurableT.
        - exact : measurableT.
      Qed.
      

      (*Définition replongeant l'événement CQ_good_event dans son espace sur Sc , en y rajoutant la condition
         que ds <= b - a*)
      Definition CQ_interval_good_event_d (a b d : nat) : set (Sc.-tuple T) :=
        match boolP (a < b)%N with
        | AltTrue Hab =>
            match boolP (b <= Sc)%N with
            | AltTrue Hb =>
                match boolP (d <= b - a)%N with
                | AltTrue Hd => [set r | CQ_good_event Hab Hb (tuple_interval_index_fun r Hab Hb)]
                | _ => setT
                end
            | _ => setT
            end
        | _ => setT
        end.
      

      (*On montre que le l'événement prenant en compte ds <= b - a est mesurable*)
      Lemma CQ_interval_good_event_d_measurable :
        forall a b d, measurable (CQ_interval_good_event_d a b d).
      Proof.
        move => a b d'.
        have Hm := measurable_interval_good a b.
        rewrite /CQ_interval_good_event in Hm.
        rewrite /CQ_interval_good_event_d.
        rewrite //=.
        destruct (boolP (a < b)%N) as [Hab | Hnab].
        - destruct (boolP (b <= Sc)%N) as [HbSc | HnbSc].
          + destruct (boolP (d' <= b - a)%N) as [Hd'ba | Hnd'ba].
            apply Hm.
          + by [].
        - by [].
        by [].
      Qed.
      


     (*événement correspondant  à l'intersection de tout les sous intervalles [a,b) qui est 
     réalisé si pour chaque intervalle admissible , l'événement CQ_interval_good_event_d a b d , est réalisé*)
     Definition fall_ab_CQ_prob (d : nat) :=
        \bigcap_(a < Sc)
        ( \bigcap_(b < Sc.+1) CQ_interval_good_event_d a b d).


     (*l'événement de l'intersection de tout les sous intervalles est mesurable*) 
      Lemma  fall_ab_CQ_prob_measurable d':
        measurable (fall_ab_CQ_prob d').
      Proof.
        rewrite /fall_ab_CQ_prob.
        Search "bigcup_measurable".
        apply bigcap_measurable.
        have OS0 := Ordinal n_sup_O.
        by (exists (Ordinal n_sup_O)).
        move => k Hk.
        apply bigcap_measurable.
        by (exists 0).
        move => k' H'.
        apply CQ_interval_good_event_d_measurable.
      Qed.
        

      (*Preuve non finie de l'implication entre fall_ab_CQ_prob et CQ_slot_advantage qui dénote que pour tout sous intervalle on a un avantage honnete*)
      Lemma fall_ab_CQ_prob_implies_CQ_slot_advantage_all  :
        fall_ab_CQ_prob ds r_cq
        -> CQ_slot_advantage w_cq ds.
      Proof.
        move => HfP.
        (*rewrite /CQ_slot_advantage.*)
        rewrite /fall_ab_CQ_prob in HfP.
        move => a b Hab Hb Hds.
        have HaSc : (a < Sc)%N.
        {
          apply (ltn_leq_trans Hab Hb).
        }

        have HbSc : (b < Sc.+1)%N.
        {
          by rewrite (ltnS b Sc).
        }
 
        pose ia := Ordinal HaSc.
        pose ib := Ordinal HbSc.
        (*rewrite -(ler_nat R).*)
        (*rewrite -(Ls_r_range_link Hab Hb). *)
        (*Search ( (_ + _ )%:R = (_ : R) + (_ : R)). *)
        (*rewrite (natrD R (| adv_slots_range a b |) w_cq). *)
        (*rewrite-(As_r_range_link Hab Hb). *)
        rewrite /bigcap /= in HfP.
        (*rewrite *)
        (*specialize (Hfp a b )*)
      Abort.
      (*t*)
     End ChainQuality.

(* ==================================================================== *)
(* Common Prefix                                                        *)
(* ==================================================================== *)

    Section CommonPrefix.

      Variables (N N' : GlobalState).
      Hypothesis N_from_initial : N0 ⇓ N .
      Hypothesis N'_from_N :  N ⇓^+ N'.
      Hypothesis N'_is_forgin_free : forging_free N'.
      Hypothesis N'_is_collision_free : collision_free N'.
      Hypothesis N'_now_is_Sc : (t_now N' = Sc)%N.
      (*party assumptions corresponding to CG assumptions for now*)
      Variables (p1 p2 : Party).
      Hypothesis p1_honest : is_honest p1.
      Hypothesis p2_honest : is_honest p2.

      (*LocalState assumption to ling p1 and l1 to N, and p2 and l2 to N'*)
      Variable (l1 l2 : LocalState).
      Hypothesis l1_p1_state : has_state p1 N l1.
      Hypothesis l2_p2_state : has_state p2 N' l2.

      Variables (k : nat).

      Variable epsilon : R.

      (*Lemme qui permet de verifier que si on à l'esperance de superslots superieure a 2 fois l'esperance d'adversarial
         , alors , si le nombre compté par le modèle probabiliste de super slot est plus grand que son esperance, et que le nombre
         d'adversarial slots est inférieur à son esperance, alors on peut en déduire par transitivité que le nombre 
         de super slot est supérieur a 2 fois le nombre d'adversarial slots*)
      Lemma SS_gt_2AS :
        let XSS := bool_trial_value SS in
        let XAS := bool_trial_value AS in
        let muSS := 'E_(\X_Sc P)[XSS] in
        let muAS := 'E_(\X_Sc P)[XAS] in
        ( ((1+deltaAs) * fine muAS) *+ 2) < (1 - deltaSs) * fine muSS ->
        forall r,
          (1+deltaAs) * fine muAS > AS_r r ->
          ((1-deltaSs) * fine muSS) < SS_r r ->
          (SS_r r> (AS_r r) *+ 2).
      Proof.
        move => XSS XAS muSS muAS H1 r H11 H12.
        have H112T :
          AS_r r *+ 2< ((1 + deltaAs) * fine muAS) *+ 2.
        {
          rewrite  ltr_wpMn2r.
          - rewrite //=.
          - rewrite //=.
          apply H11.
        }
        apply: (lt_trans H112T).
        apply: (lt_trans H1).
        apply H12.
      Qed.
      

      (*lemme d'isolation de epsilon à gaiche de l'inéquation, le calcul est retrouvable dans le papier*)
      Lemma epsilon_condition_CP :
        (1 - deltaSs) * ((pAs *+ 2) + epsilon) >
        (1 + deltaAs) * (pAs *+ 2) <->
        epsilon > (((1 + deltaAs) / (1 - deltaSs)) - 1) * (pAs *+ 2).
      Proof.
        split.
        - move => H.
          rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon) ) in H.
          rewrite -(ltr_pdivrMr (pAs *+ 2 + epsilon)) in H.
          rewrite (mulrC (1 + deltaAs)) in H.
          rewrite (mulrC (pAs *+ 2)) in H.
          rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaSs)^-1))  mulrA.
          apply H.
          rewrite subr_gt0.
          move/andP : delta_range_Ss => [H1 H2].
          apply H2.
        move => H.
        rewrite (mulrC (1 - deltaSs) (pAs *+ 2 + epsilon) ).
        rewrite -(ltr_pdivrMr (pAs *+ 2 + epsilon)).
        rewrite (mulrC (1 + deltaAs)).
        rewrite (mulrC (pAs *+ 2)).
        rewrite mulrBl mulrC mulrC ltrBlDr mul1r (addrC epsilon) -mulrA (mulrC ((1 - deltaSs)^-1))  mulrA in H.
        apply H.
        rewrite subr_gt0.
        move/andP : delta_range_Ss => [H1 H2].
        apply H2.
      Qed.
      

      (*Bon événenement probabiliste sur le nombre de superslots*)
      Definition SS_good_event :=
        let X' := bool_trial_value SS in
        let muSS := 'E_(\X_Sc P)[X'] in
        [set r | (1 - deltaSs) * fine muSS < X' r].
      
      (*mesurabilité du bon événement probabiliste sur le nombre de super slots*)
      Lemma SS_measurable_good_event_CP :
        measurable SS_good_event.
      Proof.
        set X' := bool_trial_value SS.
        set muSS := 'E_(\X_Sc P)[X'].
        rewrite /SS_good_event.
        rewrite -/X'.
        rewrite -/muSS.
        set B := (1 - deltaSs) * fine muSS.
        rewrite set_lt_eq_neg_le.
        apply : measurableC.
        rewrite -(ST_Set [set r |  X' r <= B]).
        apply: (measurable_fun_le (D := setT) (f := X' ) (g := fun _ => B)).
        - apply : measurableT.
        - rewrite //=.
          have Hcomp :
            [set r | X' r < B] = [set r | ~~ (B <= X' r)].
          {
            apply /seteqP.
            split.
            - move => r //= Hr ; by rewrite -ltNge.
            move => r //= Hr. by rewrite -ltNge in Hr.
          }
          rewrite //=.
      Qed.
      

      (*bon événement probabiliste sur le nombre d'adversarial slots*)
      Definition AS_good_event_CP :=
        let X' := bool_trial_value AS in
        let muAS := 'E_(\X_Sc P)[X'] in
        [set r | (1 + deltaAs) * fine  muAS > X' r].
      
      (*mesurabilité du bon événement probabiliste sur le nombre d'adversarial slots*)
      Lemma AS_measurable_good_event_CP :
        measurable AS_good_event_CP.
      Proof.
        rewrite /AS_good_event_CP.
        set X' := bool_trial_value AS.
        set muAS := 'E_(\X_Sc P)[X'].
        set B := (1 + deltaAs) * fine muAS.
        rewrite -/B.
        have Hcomp :
          [set r | X' r < B] = [set r | ~~ (B <= X' r)].
        {
          apply /seteqP.
          split.
          - move => r //= Hr ; by rewrite -ltNge.
          move => r //= Hr. by rewrite -ltNge in Hr.
        }
        rewrite -/B.
        rewrite Hcomp.
        have HsetNcomp :
          [set r | ~~ (B <= X' r)] = ~` [set r | B <= X' r].
        {
          apply /seteqP.
          split.
          - move => r Hr.
            rewrite //=.
            rewrite //= in Hr.
            move /negP in Hr.
            apply : Hr.
          - move => r Hr.
            rewrite //=.
            rewrite //= in Hr.
            move /negP in Hr.
            apply Hr.
        }
        rewrite  HsetNcomp.
        apply measurableC.
        rewrite -(ST_Set ([set r | B <= X' r])).
        apply: (measurable_fun_le (D := setT) (f := fun _ => B) (g := X')).
        - by apply: measurableT.
        - rewrite  //=.
        rewrite //=.
      Qed.
      

      (*Intersection entre les deux bons événements probabilistes*)
      Definition CP_good_event :=
        SS_good_event `&` AS_good_event_CP.
      

      (*réecriture d'une union sous sa forme complémentaire (1 - union des deux événement complémentaires)*)
      Lemma union_bound_SS_AS_CP :
        (\X_Sc P) (SS_good_event `&` AS_good_event_CP)
        =
        (1%R%:E - (\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP)))%E.
      Proof.
        rewrite -probability_setC.
        - congr ((\X_Sc P) _).
          apply /seteqP.
          split.
          + move => r [Hl Hr].
            move => [Hll | Hrr].
            + rewrite //=.
            rewrite //=.
          + move => r H.
            split.
            * apply : Classical_Prop.NNPP => HSS.
              apply : H.
              by left.
            apply : Classical_Prop.NNPP => HAS.
            apply : H.
            by right.
        - apply : measurableU.
          + apply measurableC.
            apply SS_measurable_good_event_CP.
          apply measurableC.
          apply AS_measurable_good_event_CP.
      Qed.


      (* ------------------------------------------------------------------ *)
      (* Interval model used by timed common prefix                          *)
      (* ------------------------------------------------------------------ *)

      Lemma b_le_t_now_N2_implies_b_le_SC (b : nat):
        (b <= t_now N')%N -> (b <= Sc)%N.
      Proof.
        move => HTN.
        by rewrite N'_now_is_Sc in HTN.
      Qed.

      Search ((?a <= ?b)%N -> (?a - 1 <= ?b)%N).

      Lemma sub1_leq (a b : nat):
        (a <= b)%N -> ((a - 1) <= b)%N.
      Proof.
        move => H.
        have Ha : ((a - 1) <= a)%N.
        {
          apply  (leq_subr 1 (a)).
        }
        apply (leq_trans Ha H).
      Qed.
      

      (*Hypothèses de liaison sur le nombre de super et adversarial slots entre le protocole et le modèle probabiliste
      sur un intervalle [a,b)*)
      Hypothesis Ss_r_range_link :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
               (r : Sc.-tuple T),
          bool_trial_value (SS_sub Hab Hb)
            (tuple_interval_index_fun r Hab Hb)
          = | super_slots_range a b |%:R.

      Hypothesis As_r_range_link_CP :
        forall a b (Hab : (a < b)%N) (Hb : (b <= Sc)%N)
               (r : Sc.-tuple T),
          bool_trial_value (AS_sub Hab Hb)
            (tuple_interval_index_fun r Hab Hb)
          = | adv_slots_range a b |%:R.
    

      (*réécriture du bon événement bon événement probabiliste pour Common Prefix sur un intervalle [a,b) donné*)
      Definition CP_good_event_interval
         (a b : nat) (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :=
        [set r : Sc.-tuple T |
          ((bool_trial_value (AS_sub Hab Hb)
              (tuple_interval_index_fun r Hab Hb)) *+ 2
           < bool_trial_value (SS_sub Hab Hb)
              (tuple_interval_index_fun r Hab Hb))%R].
      

      (*réécriture sous forme (match with) pour avoir des preuves plus simples*)
      Definition CP_good_event_interval' (a b : nat)  :=
        match boolP (a < b)%N with
        | AltTrue Hab =>
            match boolP (b <= Sc)%N with
            | AltTrue Hb => CP_good_event_interval Hab Hb
            | _ => setT
            end
        | _ => setT
        end.
      

      (*événment du protocole qu'il y ait plus de super slots que 2 fois le nombre d'adversarial slots sur un intervale [a,b)*)
      Definition interval_advantage_CP (a b : nat) : Prop :=
        ((((| adv_slots_range a b |)%:R : R) *+ 2
            < ((| super_slots_range a b |)%:R : R)))%R.
      

      (*événement du protocole qui dénote la précondition quantitative (mais probabiliste car on untilise CP_good_event_intervalle)
         sur le nombre de slots de timed_common_prefix, il contient un forall ce qui pourra rendre les preuves de mesurabilité et 
         d'implication compliquées , un passage à un événement de la forme bigcap serait probablement bénéfique
      *)
      Definition CP_good_event_set : set (Sc.-tuple T) :=
        [set r : Sc.-tuple T |
          forall (t1 t2 : nat)
                 (Htk : (t1 <= k)%N)
                 (Ht2 : (t_now N <= t2 <= t_now N')%N)
                 (Ht1t2 : ((t1 + 1) < (t2 - 1))%N)
                 (Ht2Sc : ((t2 - 1) <= Sc)%N),
            CP_good_event_interval Ht1t2 Ht2Sc r
        ].
      

      (*Lemme d'implication entre la partie probabiliste et la partie protocole sur un intervalle fixé*)
      Lemma CP_good_interval_implies_advantage
          (a b : nat) (r : Sc.-tuple T)
          (Hab : (a < b)%N) (Hb : (b <= Sc)%N) :
        CP_good_event_interval Hab Hb r -> interval_advantage_CP a b.
      Proof.
        move => H.
        rewrite /interval_advantage_CP.
        rewrite -(Ss_r_range_link Hab Hb r) -(As_r_range_link_CP Hab Hb r).
        rewrite /CP_good_event_interval //= in H.
      Qed.
      (*
      (*Lemme non fini d'implication entre le bon événement probabiliste sur tout les intervales , vers l'événement du protocole qui dénote
      la précondition quantitative de Common Prefix*)
      Lemma CP_good_event_implies_TCP (r : Sc.-tuple T) :
        CP_good_event_set r -> TCP_Good_event k.
      Proof.
        move => H.
        apply  timed_common_prefix' with (p1 := p1) (p2 := p2) ; try easy.
        rewrite /CP_good_event_set //= in H.
        move => t0 t3 Ht0 Ht3.

        have Ht0t3 : ((t0 - 1) < (t3 - 1))%N.
        {

        }

        have Ht3sc : ((t3 - 1) <= Sc)%N.
        {
          case /andP : Ht3 =>  Ht31 Hr32.
          rewrite N'_now_is_Sc in Hr32.
          have Ht3't3 : (t3 - 1 <= t3)%N.
          {
            by rewrite sub1_leq.
          }
          apply (leq_trans  Ht3't3 Hr32).
        }

        eapply H.
      Abort.
       *)
      

      (*inégalité de boole sur les deux événements complémentaire transformant ainsi l'union en un addition*)
      Lemma bad_event_union_bound_CP :
        ((\X_Sc P) ((~` SS_good_event) `|` (~` AS_good_event_CP))%E
         <=
        ((\X_Sc P) (~` SS_good_event)) + ((\X_Sc P) (~` AS_good_event_CP)))%E.
      Proof.
        apply : measureU2 ; apply : measurableC.
        - apply : SS_measurable_good_event_CP.
        apply : AS_measurable_good_event_CP.
      Qed.

      Search ((?a + ?b)%N).
      

      (*Borne inférieure sur la prorbabilité qu'on ait sur Sc
        l'intersection des deux bons événements proabbilistes*)
      Theorem CP_good_event_lower_bound :
        let XSS' := bool_trial_value SS in
        let muSS := 'E_(\X_Sc P)[XSS'] in
        let XAS' := bool_trial_value AS in
        let muAS := 'E_(\X_Sc P)[XAS'] in
        ((1%R%:E -
        ((expR (-(fine muSS * deltaSs ^+ 2) / 2)%R)%:E) -
        ((expR (-(fine muAS * deltaAs ^+ 2) / 3)%R)%:E))%E
        <=
        (\X_Sc P) CP_good_event)%E.
      Proof.
        rewrite union_bound_SS_AS_CP.
        set U := (\X_Sc P) (~` SS_good_event `|` ~` AS_good_event_CP).
        cbv zeta.
        rewrite -addeA.
        rewrite leeD2l.
        - by [].
        rewrite /U.
        rewrite -oppeD.
        - rewrite leeN2.
          apply (le_trans bad_event_union_bound_CP).
          rewrite leeD.
          + by [].
        rewrite /SS_good_event.
        apply: (le_trans _ (sampling_ineq3 pSs01 SS delta_range_Ss)).
        apply : le_measure.
        * rewrite inE.
          rewrite -try3.
          rewrite -(ST_Set ([set r | bool_trial_value SS r <= (1 - deltaSs) * fine 'E_(\X_Sc P)[(bool_trial_value SS) ] ] ) ).
          apply: (measurable_fun_le (D := setT)).
          -- apply : measurableT.
          -- rewrite //=.
          rewrite //=.
        * rewrite inE.
          rewrite -(ST_Set ([set i | bool_trial_value SS i <= (1 - deltaSs) * fine 'E_(\X_Sc P)[(bool_trial_value SS)] ] ) ).
          apply: (measurable_fun_le (D := setT)).
          -- apply : measurableT.
          -- rewrite //=.
          rewrite //=.
        move => r Hr.
        rewrite -try3 in Hr.
        exact: Hr.
        rewrite /AS_good_event_CP.
        rewrite -try2.
        apply (sampling_ineq2 pAs01 AS n_sup_O delta_range_As).
        rewrite //=.
      Qed.

    End CommonPrefix.

End PoSProbabilityBounds.

