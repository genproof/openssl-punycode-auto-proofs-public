(* Law rfc_digit_case (harness/rfc_digit_case.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_digit_case.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require OpensslPunycode.proof.laws.rfc_digit_case.RdcLawG.
Require OpensslPunycode.proof.laws.rfc_digit_case.RdcLawE1.
Require OpensslPunycode.proof.laws.rfc_digit_case.RdcLawE2.

Lemma rfc_digit_case_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_digit_case.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rfc_digit_case.whole_prog with OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.CS
    OpensslPunycode.proof.laws.rfc_digit_case.RdcLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rfc_digit_case.RdcLawE1.entries_G1).
    + exact OpensslPunycode.proof.laws.rfc_digit_case.RdcLawE2.entries_G2.
Qed.
