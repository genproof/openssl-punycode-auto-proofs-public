(* The seven body proofs of the helpers of harness/laws_common.h as one statement, `common_bodies_stmt`: the
   specifications are those of HelperSpec.v, each body under the context of exactly what it calls.  Every law lemma
   <law>_proved of src/proof/laws/<law>/ is stated with it as hypothesis (CommonBodies.v proves it); the law proofs
   use the body lemmas of Cmn*.v directly. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.harness.rj_decode_any.code.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Definition common_bodies_stmt : Prop :=
  semax_body Vprog Gprog_upto f_upto upto_spec /\
  semax_body Vprog Gprog_any_bytes f_any_bytes any_bytes_spec /\
  semax_body Vprog Gprog_any_uints f_any_uints any_uints_spec /\
  semax_body Vprog Gprog_copy_of f_copy_of copy_of_spec /\
  semax_body Vprog Gprog_none OpensslPunycode.harness.rj_decode_any.code.f_bytes_eq bytes_eq_spec /\
  semax_body Vprog Gprog_none f_uints_eq uints_eq_spec /\
  semax_body Vprog Gprog_none f_last_delimiter last_delimiter_spec.
