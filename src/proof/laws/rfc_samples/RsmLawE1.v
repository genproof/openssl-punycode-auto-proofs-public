(* Law rfc_samples: the entries of G1 (main and the helpers of harness/laws_common.h, whose bodies are proved in
   src/proof/laws/common/Cmn*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnUintsEq.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require OpensslPunycode.proof.laws.rfc_samples.RsmMain.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmLawG.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.laws.rfc_samples.RsmMain.body_main eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints.
    entry_shared' OpensslPunycode.proof.laws.common.CmnUintsEq.body_uints_eq.
    apply Forall_nil.
Qed.
