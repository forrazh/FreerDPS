From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnum ssralg reals
  interval_inference.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib.
From FreerDPS Require Import Core.
From EG.ping Require Import interfaces lossy_round_trip_impure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

(**
  Small bridge between [interfaces.v]'s ping/pong vocabulary and the impure
  probabilistic round-trip model.
 *)

Module InterfacesLossyRoundTripImpure.

Module LRT := LossyRoundTripImpure.

Section bridge.
  Context {R : realType}.
  Context {ix : interface}.
  Context `{Provide ix (@prob_interface R)}.
  Context {im : impureMonad ix}.

  Definition message_to_packet (m : M) : LRT.packet :=
    match m with
    | ping => LRT.Ping
    | pong => LRT.Pong
    end.

  Definition packet_to_message (p : LRT.packet) : M :=
    match p with
    | LRT.Ping => ping
    | LRT.Pong => pong
    end.

  Definition option_packet_to_message (p : option LRT.packet) : option M :=
    match p with
    | Some p => Some (packet_to_message p)
    | None => None
    end.

  Definition lossy_transmit (delivery : {prob R}) (m : M) : im (option M) :=
    bind (LRT.transmit delivery (message_to_packet m)) (fun delivered =>
      Ret (option_packet_to_message delivered)).

  Definition lossy_client_send (delivery : {prob R}) : im (option M) :=
    lossy_transmit delivery ping.

  Definition lossy_server_reply (delivery : {prob R}) (incoming : option M)
    : im (option M) :=
    match incoming with
    | Some ping => lossy_transmit delivery pong
    | Some pong => Ret None
    | None => Ret None
    end.

  Definition lossy_client_receive (incoming : option M) : im LRT.outcome :=
    match incoming with
    | Some pong => Ret LRT.GotPong
    | Some ping => Ret LRT.LostPong
    | None => Ret LRT.LostPong
    end.

  Definition ping_pong_once_over_interfaces (delivery : {prob R})
    : im LRT.outcome :=
    bind (lossy_client_send delivery) (fun to_server =>
      match to_server with
      | Some ping =>
          bind (lossy_server_reply delivery to_server) lossy_client_receive
      | Some pong => Ret LRT.LostPing
      | None => Ret LRT.LostPing
      end).

  Fixpoint ping_pong_retry_over_interfaces (delivery : {prob R}) (fuel : nat)
    : im LRT.outcome :=
    match fuel with
    | O => ping_pong_once_over_interfaces delivery
    | S fuel' =>
        bind (ping_pong_once_over_interfaces delivery) (fun result =>
          match result with
          | LRT.GotPong => Ret LRT.GotPong
          | LRT.LostPing | LRT.LostPong =>
              ping_pong_retry_over_interfaces delivery fuel'
          end)
    end.

  Definition delivery_probability (loss : {prob R}) : {prob R} :=
    LRT.delivery_probability loss.

  Definition ping_pong_once_success_over_interfaces (loss : {prob R})
    : im bool :=
    LRT.observe_success
      (ping_pong_once_over_interfaces (delivery_probability loss)).

  Definition ping_pong_retry_success_over_interfaces
      (loss : {prob R}) (fuel : nat) : im bool :=
    LRT.observe_success
      (ping_pong_retry_over_interfaces (delivery_probability loss) fuel).

  Lemma packet_to_messageK : cancel message_to_packet packet_to_message.
  Proof. by case. Qed.

  Lemma lossy_transmit_certain m :
    prob_rel _ (lossy_transmit 1%:i01 m) (Ret (Some m)).
  Proof.
    rewrite /lossy_transmit.
    apply: prob_rel_trans.
    - apply: prob_rel_bind_congr.
      + exact: (LRT.transmit_certain (im:=im) (message_to_packet m)).
      + move=> delivered; exact: prob_rel_refl.
    rewrite bindretf /= /option_packet_to_message packet_to_messageK.
    exact: prob_rel_refl.
  Qed.

  Lemma received_pong_over_interfaces (m : M) :
    LRT.received_pong (if m is pong then LRT.GotPong else LRT.LostPong)
    = match m with ping => false | pong => true end.
  Proof. by case: m. Qed.

End bridge.

End InterfacesLossyRoundTripImpure.
