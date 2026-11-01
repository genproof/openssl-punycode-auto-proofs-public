(* Law rfc_basic_first (harness/rfc_basic_first.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_basic_first.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.
Require OpensslPunycode.proof.laws.rfc_basic_first.RbfLawG.
Require OpensslPunycode.proof.laws.rfc_basic_first.RbfLawE1.
Require OpensslPunycode.proof.laws.rfc_basic_first.RbfLawE2.

Lemma rfc_basic_first_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_basic_first.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rfc_basic_first.whole_prog with OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.CS
    OpensslPunycode.proof.laws.rfc_basic_first.RbfLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rfc_basic_first.RbfLawE1.entries_G1).
    + exact OpensslPunycode.proof.laws.rfc_basic_first.RbfLawE2.entries_G2.
Qed.
