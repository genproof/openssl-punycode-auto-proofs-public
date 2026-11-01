(* Law rj_decode_any (harness/rj_decode_any.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rj_decode_any.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rj_decode_any.JdaProg.
Require OpensslPunycode.proof.laws.rj_decode_any.JdaLawG.
Require OpensslPunycode.proof.laws.rj_decode_any.JdaLawE1.
Require OpensslPunycode.proof.laws.rj_decode_any.JdaLawE2.

Lemma rj_decode_any_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rj_decode_any.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rj_decode_any.whole_prog with OpensslPunycode.proof.laws.rj_decode_any.JdaProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rj_decode_any.JdaProg.CS
    OpensslPunycode.proof.laws.rj_decode_any.JdaLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rj_decode_any.JdaLawE1.entries_G1).
    + exact OpensslPunycode.proof.laws.rj_decode_any.JdaLawE2.entries_G2.
Qed.
