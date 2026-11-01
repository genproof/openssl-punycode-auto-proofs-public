(* Law api_a2ulabel_labels (harness/api_a2ulabel_labels.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.api_a2ulabel_labels.
(* The proof does not use the hypothesis: the helpers' bodies are proved under the specifications of
   src/proof/laws/common/HelperSpec.v (Cmn*.v), each under the context of exactly what it calls, which this law's
   program can take in (AlbLawE1.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbLawG.
Require OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbLawE1.
Require OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbLawE2.

Lemma api_a2ulabel_labels_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.api_a2ulabel_labels.whole_prog.
Proof.
  intros _. change OpensslPunycode.contracts.api_a2ulabel_labels.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbLawE2.entries_G2.
Qed.
