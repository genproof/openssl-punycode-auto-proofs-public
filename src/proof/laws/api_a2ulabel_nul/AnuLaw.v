(* Law api_a2ulabel_nul (harness/api_a2ulabel_nul.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them).
   The hypothesis is not used: the helpers' bodies are proved under the specifications of
   src/proof/laws/common/HelperSpec.v (Cmn*.v), each under the context of exactly what it calls, which a law
   whose program has only those functions can take in (AnuLawE1.v).  The law's content is the model fact
   AnuModel.a2ulabel_nul: on success the octets written are nonzero octets, then the NUL, within outlen. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.api_a2ulabel_nul.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawG.
Require OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawE1.
Require OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawE2.

Lemma api_a2ulabel_nul_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.api_a2ulabel_nul.whole_prog.
Proof.
  intros _. change OpensslPunycode.contracts.api_a2ulabel_nul.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawE2.entries_G2.
Qed.
