(* Law decode: the entries of G1 (main and the harness's functions). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.harness.BodiesRt.
Require OpensslPunycode.proof.harness.BodyDecRef.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require OpensslPunycode.proof.harness.decode.DecMain.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecLawG.

Module RB := OpensslPunycode.proof.harness.BodiesRt.
Module DB := OpensslPunycode.proof.harness.BodyDecRef.

Lemma entries_G1 : Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.harness.decode.DecMain.body_main eq_refl).
    entry_shared' RB.body_copy_bytes.
    entry_shared' RB.body_same_bytes.
    entry_shared' RB.body_same_uints.
    entry_shared' DB.body_pr_decode.
    entry_shared' DB.body_pr_digit_value.
    entry_shared' RB.body_pr_threshold.
    entry_shared' RB.body_pr_adapt.
    apply Forall_nil.
Qed.
