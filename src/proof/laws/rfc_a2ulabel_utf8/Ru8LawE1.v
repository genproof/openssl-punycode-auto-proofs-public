(* Law rfc_a2ulabel_utf8: the entries of G1 (main; the helpers of laws_common.h it calls, whose bodies are proved in
   src/proof/laws/common/Cmn*.v; the harness's own utf8, proved in Ru8Utf8Body.v). *)
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
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Main.
Require OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Utf8Body.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8LawG.

Module C := OpensslPunycode.proof.laws.common.HelperSpec.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Main.body_main eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes.
    entry_shared' OpensslPunycode.proof.laws.common.CmnCopyOf.body_copy_of.
    entry_shared' OpensslPunycode.proof.laws.common.CmnBytesEq.body_bytes_eq.
    entry_shared' OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Utf8Body.body_utf8.
    apply Forall_nil.
Qed.
