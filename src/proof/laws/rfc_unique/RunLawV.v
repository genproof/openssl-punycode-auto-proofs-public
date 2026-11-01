(* Law rfc_unique: harness_safe of its program, from the model fact RunUniqStmt.unique_stmt (the main of
   harness/rfc_unique.c on the specifications of ossl_punycode_decode and of the helpers of laws_common.h). *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.
Require OpensslPunycode.contracts.rfc_unique.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunLawG.
Require OpensslPunycode.proof.laws.rfc_unique.RunLawE1.
Require OpensslPunycode.proof.laws.rfc_unique.RunLawE2.

(* The main (RunMain.v, in pieces RunMainP*.v) and the bodies of the functions it reaches (the helpers of
   laws_common.h: their specifications src/proof/laws/common/HelperSpec.v, their bodies Cmn*.v), assembled by
   QuickProof.Assembly.  The checks of main hold by the model fact: two inputs that ossl_punycode_decode decodes,
   with the same capacity, into the same code points are the same octets up to the case of letters among the
   deltas. *)
Lemma rfc_unique_of_model :
  OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.unique_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_unique.whole_prog.
Proof.
  intros Hu. change (harness_safe p).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact (OpensslPunycode.proof.laws.rfc_unique.RunLawE1.entries_G1 Hu).
    + exact OpensslPunycode.proof.laws.rfc_unique.RunLawE2.entries_G2.
Qed.
