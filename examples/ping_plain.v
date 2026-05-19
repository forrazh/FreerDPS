From monae Require Import preamble hierarchy.

(* From mathcomp Require Import unstable mathcomp_extra ring lra reals Rstruct. *)
(* From infotheo Require Import realType_ext ssr_ext fsdist convex. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrfun seq path.
From FreerDPS Require Import Impure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables. 
Local Open Scope monae_scope.

Inductive M := ping|pong.

Inductive IC : interface :=
| SEND (m : M) : IC M
| WAIT (m : M) : IC M.

Definition send `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SEND ping).
Definition wait `{Provide ix IC} {im : impureMonad ix} := trigger (im:=im) (inj_p $ WAIT pong).

Definition C `{Provide ix IC} {im : impureMonad ix} := send (im:=im) >> wait.

(* ------------------------------------------------------------------------------------ *)

Inductive IS : interface :=
| RECV (m : M) : IS M
| SNED (m : M) : IS M.

Definition sned `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ SNED pong).
Definition recv `{Provide ix IS} {im : impureMonad ix} := trigger (im:=im) (inj_p $ RECV ping).

Definition S `{Provide ix IS} {im : impureMonad ix} {T} : im T -> im T := fun (X : im T) => recv (im:=im) >> sned >> X.

(* ------------------------------------------------------------------------------------ *)
(* Inductive IN : interface :=
| DLVR (m : M) : IN M
| DROP (m : M) : IN M.

Definition deliver `{Provide ix IN} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DLVR m).
Definition drop `{Provide ix IN} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DROP m). *)

Inductive N : interface :=
| DELIVER (m : M) : N (option M). 
(* Message may be dropped *)

Definition deliver `{Provide ix N} {im : impureMonad ix} (m : M) := trigger (im:=im) (inj_p $ DELIVER m).


(* ------------------------------------------------------------------------------------ *)

(**
    Now, lets try to model this :

(a)    +---+ ==> (1) send ping ==> +---+ ==> (2) dlvr ping ==> +---+ 
       | C |                       | N |                       | S |
(b)    +---+ <== (4) dlvr pong <== +---+ <== (4) send pong <== +---+

**)

Definition simple_one_round_fail_prog `{Provide ix IC, Provide ix IS, Provide ix N} {im : impureMonad ix} : im unit :=

(* (a) *)    send (im:=im) >>= fun m => deliver m >>= fun om => match om with | Some _ => recv >> 
(* (b) *)    sned          >>= fun m => deliver m >>= fun om => match om with | Some _ => wait >> Ret tt
    | _ => Ret tt end 
| _ => Ret tt    
    end.
 (* Ret tt. *)