(* Law rfc_unique: the entries of G1 (main, from the model fact, and the helpers of harness/laws_common.h, whose
   bodies are proved in src/proof/laws/common/Cmn*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyBytes.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnUintsEq.
Require OpensslPunycode.proof.laws.common.CmnLastDelim.
Require OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require OpensslPunycode.proof.laws.rfc_unique.RunMain.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunLawG.

Lemma entries_G1 : OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.unique_stmt ->
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
  intros Hu.
    entry_shared' (semax_body_main_std _ _ p _ _
      (OpensslPunycode.proof.laws.rfc_unique.RunMain.body_main Hu) eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints.
    entry_shared' OpensslPunycode.proof.laws.common.CmnUintsEq.body_uints_eq.
    entry_shared' OpensslPunycode.proof.laws.common.CmnLastDelim.body_last_delimiter.
    apply Forall_nil.
Qed.
