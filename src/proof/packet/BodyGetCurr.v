(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma body_get_curr_ok : semax_body Vprog Gprog_none f_WPACKET_get_curr WPACKET_get_curr_spec.
Proof.
  start_function.
  assert_PROP (isptr buf). { entailer!. }
  forward.
  forward_if (PROP () LOCAL (temp _t'1 buf; temp _pkt pkt)
     SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (wr, (mx, (sub, Vint Int.zero)))))) pkt;
          data_at shb (tarray tuchar cap) v buf)).
  - forward. forward. entailer!.
  - destruct buf; try contradiction. discriminate.
  - forward. forward_if.
    + destruct buf; try contradiction. discriminate.
    + forward. forward_if.
      * contradiction.
      * forward. forward.
Qed.
