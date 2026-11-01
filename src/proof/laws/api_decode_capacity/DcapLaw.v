(* Law api_decode_capacity (harness/api_decode_capacity.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.api_decode_capacity.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapLawG.
Require OpensslPunycode.proof.laws.api_decode_capacity.DcapLawE1.
Require OpensslPunycode.proof.laws.api_decode_capacity.DcapLawE2.

(* The main (DcapMain.v, in pieces DcapMainP*.v) and the bodies of the functions it reaches (the helpers of
   laws_common.h: their specifications src/proof/laws/common/HelperSpec.v, their bodies Cmn*.v), assembled by
   QuickProof.Assembly.  On success with count code points, ossl_punycode_decode's specification leaves the
   elements from count on as they were (the array is the output followed by the rest of its initial values); the
   model decoder succeeds the same into exactly count elements and fails into count - 1 (DcapModel.v: the capacity
   is read only by the test against the basic code points and by the test before each insertion).  The helpers'
   bodies are proved on their own specifications, so the hypothesis on CommonSpec's bodies is not used. *)
Lemma api_decode_capacity_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.api_decode_capacity.whole_prog.
Proof.
  intros _. change (harness_safe p).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.api_decode_capacity.DcapLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.api_decode_capacity.DcapLawE2.entries_G2.
Qed.
