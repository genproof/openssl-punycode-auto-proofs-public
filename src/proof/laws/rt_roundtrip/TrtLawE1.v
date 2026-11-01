(* Law rt_roundtrip: the entries of G1 (main, the harness's encoder and its callees, the helpers of
   harness/laws_common.h, whose bodies are proved in src/proof/laws/common/Cmn*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnUintsEq.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtModel.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtMain.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtBodyEncode.
Require OpensslPunycode.proof.laws.rt_roundtrip.TrtLeaf.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtLawG.

Lemma entries_G1 :
  Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _
       (OpensslPunycode.proof.laws.rt_roundtrip.TrtMain.body_main
          OpensslPunycode.proof.laws.rt_roundtrip.TrtModel.trt_model) eq_refl).
    entry_shared' OpensslPunycode.proof.laws.common.CmnUpto.body_upto.
    entry_shared' OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints.
    entry_shared' OpensslPunycode.proof.laws.common.CmnUintsEq.body_uints_eq.
    entry_shared' OpensslPunycode.proof.laws.rt_roundtrip.TrtBodyEncode.body_encode.
    entry_shared' OpensslPunycode.proof.laws.rt_roundtrip.TrtLeaf.body_put.
    entry_shared' OpensslPunycode.proof.laws.rt_roundtrip.TrtLeaf.body_digit.
    entry_shared' OpensslPunycode.proof.laws.rt_roundtrip.TrtLeaf.body_rfc_adapt.
    apply Forall_nil.
Qed.
