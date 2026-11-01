(* Law api_a2ulabel_copy (harness/api_a2ulabel_copy.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them).
   The hypothesis is not used: the helpers' bodies are proved under the specifications of
   src/proof/laws/common/HelperSpec.v (Cmn*.v), each under the context of exactly what it calls, which a law
   whose program has only those functions can take in (AcpLawE1.v). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.api_a2ulabel_copy.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpLawG.
Require OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpLawE1.
Require OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpLawE2.

Lemma api_a2ulabel_copy_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.api_a2ulabel_copy.whole_prog.
Proof.
  intros _. change OpensslPunycode.contracts.api_a2ulabel_copy.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpLawE2.entries_G2.
Qed.
