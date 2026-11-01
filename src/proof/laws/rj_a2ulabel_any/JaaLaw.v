(* Law rj_a2ulabel_any (harness/rj_a2ulabel_any.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them).
   The hypothesis is not used: the helpers' bodies are proved under the specifications of
   src/proof/laws/common/HelperSpec.v (Cmn*.v), each under the context of exactly what it calls, which a law
   whose program has only those functions can take in (JaaLawE1.v). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rj_a2ulabel_any.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaProg.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaLawG.
Require OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaLawE1.
Require OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaLawE2.

Lemma rj_a2ulabel_any_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rj_a2ulabel_any.whole_prog.
Proof.
  intros _. change OpensslPunycode.contracts.rj_a2ulabel_any.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaLawE1.entries_G1).
    + exact OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaLawE2.entries_G2.
Qed.
