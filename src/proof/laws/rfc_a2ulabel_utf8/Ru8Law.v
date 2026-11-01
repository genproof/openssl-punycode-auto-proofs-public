(* Law rfc_a2ulabel_utf8 (harness/rfc_a2ulabel_utf8.c, with harness/laws_common.h): harness_safe of its program, given the bodies of
   the helpers of laws_common.h (src/proof/laws/common/CommonSpec.v states them, CommonBodies.v proves them).
   The hypothesis is not used: the helpers' bodies are proved under the specifications of
   src/proof/laws/common/HelperSpec.v (Cmn*.v), each under the context of exactly what it calls, which a law
   whose program has only those functions can take in (Ru8LawE1.v).  The law's content is the model fact
   Ru8Model.ru8_a2ulabel: for "xn--" ++ s, a2ulabel gives the UTF-8 octets of the decoding of s and a NUL (1 when
   they fit, 0 when not), or -1 without a decoding; the harness's utf8 computes Model.utf8 (Ru8Utf8Body.v). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_a2ulabel_utf8.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawG.
Require OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawE1.
Require OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawE2.

Lemma rfc_a2ulabel_utf8_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_a2ulabel_utf8.whole_prog.
Proof.
  intros _. change OpensslPunycode.contracts.rfc_a2ulabel_utf8.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawE1.entries_G1.
    + exact OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawE2.entries_G2.
Qed.
