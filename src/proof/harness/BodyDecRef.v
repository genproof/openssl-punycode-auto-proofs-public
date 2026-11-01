(* The bodies of pr_digit_value and pr_decode (harness/puny_ref.h, RFC 3492 6.2), under the decode harness's
   compspecs. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require OpensslPunycode.proof.harness.DRDigitValue.
Require OpensslPunycode.proof.harness.DRMain.

Lemma decref_bodies :
  semax_body Vprog Gprog_none f_pr_digit_value pr_digit_value_spec /\
  semax_body Vprog Gprog_decode f_pr_decode pr_decode_spec.
Proof.
split.
- exact OpensslPunycode.proof.harness.DRDigitValue.body_pr_digit_value_proof.
- exact OpensslPunycode.proof.harness.DRMain.body_pr_decode_main.
Qed.

Definition body_pr_digit_value : semax_body Vprog Gprog_none f_pr_digit_value pr_digit_value_spec :=
  proj1 decref_bodies.
Definition body_pr_decode : semax_body Vprog Gprog_decode f_pr_decode pr_decode_spec :=
  proj2 decref_bodies.
