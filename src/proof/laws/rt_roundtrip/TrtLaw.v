(* Law rt_roundtrip (harness/rt_roundtrip.c, with harness/laws_common.h): harness_safe of its program.  The
   hypothesis, the bodies of the helpers of laws_common.h (CommonSpec.v), is not needed: the assembly uses their
   proofs (src/proof/laws/common/Cmn*.v) directly. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rt_roundtrip.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtLawG.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtLawE1.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtLawE2.

Lemma rt_roundtrip_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rt_roundtrip.whole_prog.
Proof.
  intros _.
  change OpensslPunycode.contracts.rt_roundtrip.whole_prog with OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.p.
  harness_safe_by_specs OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.CS
    OpensslPunycode.proof.laws.rt_roundtrip.TrtLawG.G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.rt_roundtrip.TrtLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.rt_roundtrip.TrtLawE2.entries_G2.
Qed.
