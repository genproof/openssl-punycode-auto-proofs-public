(* Law rfc_ace_any_case (harness/rfc_ace_any_case.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_ace_any_case.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.
Require OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawG.
Require OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawE1.
Require OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawE2.

Lemma rfc_ace_any_case_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_ace_any_case.whole_prog.
Proof.
  (* The helpers' bodies are proved directly (src/proof/laws/common/Cmn*.v), each under the context of exactly
     what it calls; the hypothesis is not needed. *)
  intros _.
  change OpensslPunycode.contracts.rfc_ace_any_case.whole_prog with OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.CS
    OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.rfc_ace_any_case.RacLawE2.entries_G2.
Qed.
