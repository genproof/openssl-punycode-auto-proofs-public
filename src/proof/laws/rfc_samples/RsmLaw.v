(* Law rfc_samples (harness/rfc_samples.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_samples.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require OpensslPunycode.proof.laws.rfc_samples.RsmLawG.
Require OpensslPunycode.proof.laws.rfc_samples.RsmLawE1.
Require OpensslPunycode.proof.laws.rfc_samples.RsmLawE2.

Lemma rfc_samples_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_samples.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rfc_samples.whole_prog with OpensslPunycode.proof.laws.rfc_samples.RsmProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rfc_samples.RsmProg.CS
    OpensslPunycode.proof.laws.rfc_samples.RsmLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.rfc_samples.RsmLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.rfc_samples.RsmLawE2.entries_G2.
Qed.
