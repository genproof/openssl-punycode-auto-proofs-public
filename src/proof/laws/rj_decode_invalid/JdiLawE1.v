(* Law rj_decode_invalid: the entries of G1 (main and the helpers of harness/laws_common.h, whose bodies are proved in
   src/proof/laws/common/Cmn*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyBytes.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnLastDelim.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require OpensslPunycode.proof.laws.rj_decode_invalid.JdiMain.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiLawG.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.laws.rj_decode_invalid.JdiMain.body_main eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints.
    entry_shared' OpensslPunycode.proof.laws.common.CmnLastDelim.body_last_delimiter.
    apply Forall_nil.
Qed.
