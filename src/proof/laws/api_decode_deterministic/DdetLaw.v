(* Law api_decode_deterministic (harness/api_decode_deterministic.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.api_decode_deterministic.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawG.
Require OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawE1.
Require OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawE2.

(* The main (DdetMain.v, in pieces DdetMainP*.v) and the bodies of the functions it reaches (the helpers of
   laws_common.h: their specifications src/proof/laws/common/HelperSpec.v, their bodies Cmn*.v), assembled by
   QuickProof.Assembly: two decodes of the same octets, one in place inside a larger object and one from a copy, into
   arrays of the same capacity with different initial values, give the same result, the same length and, on
   success, the same code points (ossl_punycode_decode's specification is a function of the octets and the
   capacity; the initial values only fill the array past the output). *)
Lemma api_decode_deterministic_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.api_decode_deterministic.whole_prog.
Proof.
  intros _. change (harness_safe p).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawE2.entries_G2.
Qed.
