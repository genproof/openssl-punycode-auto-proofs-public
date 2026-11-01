(* Law api_a2ulabel_nul: the entries of G1 (main and the helpers of laws_common.h it calls, whose bodies are
   proved in src/proof/laws/common/Cmn*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyBytes.
Require OpensslPunycode.proof.laws.common.CmnCopyOf.
Require OpensslPunycode.proof.laws.common.CmnBytesEq.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuProg.
Require OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuMain.
Require Import OpensslPunycode.harness.api_a2ulabel_nul.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuLawG.

Module C := OpensslPunycode.proof.laws.common.HelperSpec.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuMain.body_main eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes.
    entry_shared' OpensslPunycode.proof.laws.common.CmnCopyOf.body_copy_of.
    entry_shared' OpensslPunycode.proof.laws.common.CmnBytesEq.body_bytes_eq.
    apply Forall_nil.
Qed.
