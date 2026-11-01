(* The bodies of the small harness functions shared by every harness (pr_threshold, pr_adapt, pr_digit_char,
   pr_utf8, copy_bytes, same_bytes, same_uints), under the roundtrip harness's compspecs. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require OpensslPunycode.proof.harness.BodyRtThr.
Require OpensslPunycode.proof.harness.BodyRtAdapt.
Require OpensslPunycode.proof.harness.BodyRtCopy.
Require OpensslPunycode.proof.harness.BodyRtSameB.
Require OpensslPunycode.proof.harness.BodyRtSameU.
Require OpensslPunycode.proof.harness.BodyRtUtf8.

Lemma rt_small_bodies :
  semax_body Vprog Gprog_none f_pr_threshold pr_threshold_spec /\
  semax_body Vprog Gprog_none f_pr_adapt pr_adapt_spec /\
  semax_body Vprog Gprog_none f_pr_digit_char pr_digit_char_spec /\
  semax_body Vprog Gprog_none f_pr_utf8 pr_utf8_spec /\
  semax_body Vprog Gprog_none f_copy_bytes copy_bytes_spec /\
  semax_body Vprog Gprog_none f_same_bytes same_bytes_spec /\
  semax_body Vprog Gprog_none f_same_uints same_uints_spec.
Proof.
  exact (conj BodyRtThr.body_pr_threshold' (conj BodyRtAdapt.body_pr_adapt' (conj BodyRtThr.body_pr_digit_char'
    (conj BodyRtUtf8.body_pr_utf8' (conj BodyRtCopy.body_copy_bytes' (conj BodyRtSameB.body_same_bytes'
      BodyRtSameU.body_same_uints')))))).
Qed.

Definition body_pr_threshold : semax_body Vprog Gprog_none f_pr_threshold pr_threshold_spec :=
  proj1 rt_small_bodies.
Definition body_pr_adapt : semax_body Vprog Gprog_none f_pr_adapt pr_adapt_spec :=
  proj1 (proj2 rt_small_bodies).
Definition body_pr_digit_char : semax_body Vprog Gprog_none f_pr_digit_char pr_digit_char_spec :=
  proj1 (proj2 (proj2 rt_small_bodies)).
Definition body_pr_utf8 : semax_body Vprog Gprog_none f_pr_utf8 pr_utf8_spec :=
  proj1 (proj2 (proj2 (proj2 rt_small_bodies))).
Definition body_copy_bytes : semax_body Vprog Gprog_none f_copy_bytes copy_bytes_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 rt_small_bodies)))).
Definition body_same_bytes : semax_body Vprog Gprog_none f_same_bytes same_bytes_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 rt_small_bodies))))).
Definition body_same_uints : semax_body Vprog Gprog_none f_same_uints same_uints_spec :=
  proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rt_small_bodies))))).
