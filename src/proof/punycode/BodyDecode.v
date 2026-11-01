(* The bodies of ossl_punycode_decode and its helpers adapt, is_basic, digit_decoded (crypto/punycode.c), under
   Punycode.CS. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.BodyDecHelpers.
Require Import OpensslPunycode.proof.punycode.BodyDecMain.

Lemma decode_bodies :
  semax_body Vprog Gprog_none f_adapt adapt_spec /\
  semax_body Vprog Gprog_none f_is_basic is_basic_spec /\
  semax_body Vprog Gprog_none f_digit_decoded digit_decoded_spec /\
  semax_body Vprog Gprog_decode f_ossl_punycode_decode ossl_punycode_decode_spec.
Proof.
  destruct decode_helper_bodies as [A [B C]].
  exact (conj A (conj B (conj C body_decode_main))).
Qed.

Definition body_adapt : semax_body Vprog Gprog_none f_adapt adapt_spec := proj1 decode_bodies.
Definition body_is_basic : semax_body Vprog Gprog_none f_is_basic is_basic_spec := proj1 (proj2 decode_bodies).
Definition body_digit_decoded : semax_body Vprog Gprog_none f_digit_decoded digit_decoded_spec :=
  proj1 (proj2 (proj2 decode_bodies)).
Definition body_ossl_punycode_decode :
  semax_body Vprog Gprog_decode f_ossl_punycode_decode ossl_punycode_decode_spec :=
  proj2 (proj2 (proj2 decode_bodies)).
