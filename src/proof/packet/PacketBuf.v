(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

(* The buffer of a static WPACKET cut in three: the octets written, the next write, the rest. *)
Lemma buf_split3 {cs: compspecs}: forall sh cap buf (a b c: list val) n1 n2,
  field_compatible (tarray tuchar cap) [] buf ->
  0 <= n1 <= n2 -> n2 <= cap ->
  Zlength a = n1 -> Zlength b = n2 - n1 -> Zlength c = cap - n2 ->
  data_at sh (tarray tuchar cap) (a ++ b ++ c) buf =
  (data_at sh (tarray tuchar n1) a buf * data_at sh (tarray tuchar (n2 - n1)) b (offset_val n1 buf) *
   data_at sh (tarray tuchar (cap - n2)) c (offset_val n2 buf))%logic.
Proof.
  intros. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh cap n1 n2) by (autorewrite with sublist; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  autorewrite with sublist. reflexivity.
Qed.
