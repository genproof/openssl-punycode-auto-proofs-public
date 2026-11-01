(* Law api_decode_deterministic: the entries of G1 (main and the helpers of laws_common.h it calls). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyBytes.
Require OpensslPunycode.proof.laws.common.CmnCopyOf.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnUintsEq.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Require OpensslPunycode.proof.laws.api_decode_deterministic.DdetMain.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetLawG.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _
      OpensslPunycode.proof.laws.api_decode_deterministic.DdetMain.body_main eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes.
    entry_shared' OpensslPunycode.proof.laws.common.CmnCopyOf.body_copy_of.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints.
    entry_shared' OpensslPunycode.proof.laws.common.CmnUintsEq.body_uints_eq.
    apply Forall_nil.
Qed.
