(* The bodies of ossl_a2ulabel and codepoint2utf8 (crypto/punycode.c, patched), under Punycode.CS: BodyCp.v and
   BodyA2uMain.v (pieces A2u*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.BodyCp.
Require Import OpensslPunycode.proof.punycode.BodyA2uMain.

Lemma a2u_bodies :
  semax_body Vprog Gprog_none f_codepoint2utf8 codepoint2utf8_spec /\
  semax_body Vprog Gprog_a2ulabel f_ossl_a2ulabel ossl_a2ulabel_spec.
Proof.
  split; [apply body_cp2utf8_proof | apply body_a2ulabel_proof].
Qed.

Definition body_codepoint2utf8 : semax_body Vprog Gprog_none f_codepoint2utf8 codepoint2utf8_spec :=
  proj1 a2u_bodies.
Definition body_ossl_a2ulabel : semax_body Vprog Gprog_a2ulabel f_ossl_a2ulabel ossl_a2ulabel_spec :=
  proj2 a2u_bodies.
