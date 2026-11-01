(* The bodies of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.
Require OpensslPunycode.proof.packet.BodyInit.
Require OpensslPunycode.proof.packet.BodyInternInit.
Require OpensslPunycode.proof.packet.BodyMaxmaxsize.
Require OpensslPunycode.proof.packet.BodyMemcpy.
Require OpensslPunycode.proof.packet.BodyPutBytes.
Require OpensslPunycode.proof.packet.BodyPutValue.
Require OpensslPunycode.proof.packet.BodyAllocate.
Require OpensslPunycode.proof.packet.BodyReserve.
Require OpensslPunycode.proof.packet.BodyGetCurr.
Require OpensslPunycode.proof.packet.BodyCleanup.

Lemma packet_bodies :
  semax_body Vprog Gprog_init_static_len f_WPACKET_init_static_len WPACKET_init_static_len_spec /\
  semax_body Vprog Gprog_intern_init_len f_wpacket_intern_init_len wpacket_intern_init_len_spec /\
  semax_body Vprog Gprog_none f_maxmaxsize maxmaxsize_spec /\
  semax_body Vprog Gprog_memcpy f_WPACKET_memcpy WPACKET_memcpy_spec /\
  semax_body Vprog Gprog_put_bytes f_WPACKET_put_bytes__ WPACKET_put_bytes___spec /\
  semax_body Vprog Gprog_none f_put_value put_value_spec /\
  semax_body Vprog Gprog_allocate_bytes f_WPACKET_allocate_bytes WPACKET_allocate_bytes_spec /\
  semax_body Vprog Gprog_reserve_bytes f_WPACKET_reserve_bytes WPACKET_reserve_bytes_spec /\
  semax_body Vprog Gprog_none f_WPACKET_get_curr WPACKET_get_curr_spec /\
  semax_body Vprog Gprog_cleanup f_WPACKET_cleanup WPACKET_cleanup_spec.
Proof.
  repeat match goal with |- _ /\ _ => split end.
  - exact BodyInit.body_init_static_len_ok.
  - exact BodyInternInit.body_intern_init_len_ok.
  - exact BodyMaxmaxsize.body_maxmaxsize_ok.
  - exact BodyMemcpy.body_memcpy_ok.
  - exact BodyPutBytes.body_put_bytes_ok.
  - exact BodyPutValue.body_put_value_ok.
  - exact BodyAllocate.body_allocate_bytes_ok.
  - exact BodyReserve.body_reserve_bytes_ok.
  - exact BodyGetCurr.body_get_curr_ok.
  - exact BodyCleanup.body_cleanup_ok.
Qed.

Definition body_WPACKET_init_static_len :
  semax_body Vprog Gprog_init_static_len f_WPACKET_init_static_len WPACKET_init_static_len_spec :=
  proj1 packet_bodies.
Definition body_wpacket_intern_init_len :
  semax_body Vprog Gprog_intern_init_len f_wpacket_intern_init_len wpacket_intern_init_len_spec :=
  proj1 (proj2 packet_bodies).
Definition body_maxmaxsize : semax_body Vprog Gprog_none f_maxmaxsize maxmaxsize_spec :=
  proj1 (proj2 (proj2 packet_bodies)).
Definition body_WPACKET_memcpy : semax_body Vprog Gprog_memcpy f_WPACKET_memcpy WPACKET_memcpy_spec :=
  proj1 (proj2 (proj2 (proj2 packet_bodies))).
Definition body_WPACKET_put_bytes__ :
  semax_body Vprog Gprog_put_bytes f_WPACKET_put_bytes__ WPACKET_put_bytes___spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 packet_bodies)))).
Definition body_put_value : semax_body Vprog Gprog_none f_put_value put_value_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 packet_bodies))))).
Definition body_WPACKET_allocate_bytes :
  semax_body Vprog Gprog_allocate_bytes f_WPACKET_allocate_bytes WPACKET_allocate_bytes_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 packet_bodies)))))).
Definition body_WPACKET_reserve_bytes :
  semax_body Vprog Gprog_reserve_bytes f_WPACKET_reserve_bytes WPACKET_reserve_bytes_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 packet_bodies))))))).
Definition body_WPACKET_get_curr : semax_body Vprog Gprog_none f_WPACKET_get_curr WPACKET_get_curr_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 packet_bodies)))))))).
Definition body_WPACKET_cleanup : semax_body Vprog Gprog_cleanup f_WPACKET_cleanup WPACKET_cleanup_spec :=
  proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 packet_bodies)))))))).
