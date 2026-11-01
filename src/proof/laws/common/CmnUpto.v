(* The body of upto (harness/laws_common.h): an arbitrary size_t clipped to max. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Lemma body_upto : semax_body Vprog Gprog_upto f_upto upto_spec.
Proof.
  start_function.
  forward_call tt. Intros v.
  forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr (Z.min v max)))) SEP ()).
  - forward. entailer!. rewrite Z.min_l by lia. auto.
  - forward. entailer!. rewrite Z.min_r by lia. auto.
  - forward. Exists (Z.min v max). entailer!.
Qed.
