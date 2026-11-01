(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma body_intern_init_len_ok :
  semax_body Vprog Gprog_intern_init_len f_wpacket_intern_init_len wpacket_intern_init_len_spec.
Proof.
  start_function.
  forward. forward.
  forward_call (gv, sub_size, gv ___stringlit_packet_1, 0, fn, zf, live).
  Intros vret. destruct vret as [[[p fn'] zf'] live']. simpl fst in *. simpl snd in *.
  forward. destruct (eq_dec p nullval).
  - subst p. forward_if.
    + forward. Exists nullval fn' zf' live'. entailer!.
    + congruence.
  - unfold zblock. Intros. forward_if.
    + contradiction.
    + forward_if.
      * forward. Exists p fn' zf' live'. rewrite !if_false by auto. unfold sub_rec, zblock. entailer!.
      * congruence.
Qed.
