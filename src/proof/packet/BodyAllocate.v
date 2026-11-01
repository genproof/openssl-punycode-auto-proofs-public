(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma body_allocate_bytes_ok :
  semax_body Vprog Gprog_allocate_bytes f_WPACKET_allocate_bytes WPACKET_allocate_bytes_spec.
Proof.
  start_function.
  forward_call (shp, pkt, shb, buf, cap, v, n, sub, len, sha, pa).
  destruct (orb (len =? 0) (cap - n <? len)) eqn:E.
  - forward_if.
    + forward. cancel.
    + contradiction.
  - forward_if.
    + discriminate.
    + unfold pkt_rep. forward. forward. forward. forward. forward. unfold pkt_rep. cancel.
Qed.
