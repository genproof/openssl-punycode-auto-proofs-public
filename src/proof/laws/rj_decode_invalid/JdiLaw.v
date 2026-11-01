(* Law rj_decode_invalid (harness/rj_decode_invalid.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rj_decode_invalid.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawG.
Require OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawE1.
Require OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawE2.

Lemma rj_decode_invalid_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rj_decode_invalid.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rj_decode_invalid.whole_prog with OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.CS
    OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawE1.entries_G1).
    + exact OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawE2.entries_G2.
Qed.
