(* Law a2ulabel: the entries of G1 (main and the harness's functions). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.libc.LibcSpec OpensslPunycode.proof.libc.LibcBodies.
Require OpensslPunycode.proof.shim.ShimSpec OpensslPunycode.proof.shim.ShimBodies.
Require OpensslPunycode.proof.packet.PacketSpec OpensslPunycode.proof.packet.PacketBodies.
Require OpensslPunycode.proof.punycode.PunySpec OpensslPunycode.proof.punycode.BodyDecode.
Require OpensslPunycode.proof.punycode.BodyA2u.
Require OpensslPunycode.proof.harness.RefRt OpensslPunycode.proof.harness.BodiesRt.
Require OpensslPunycode.proof.harness.RefDec OpensslPunycode.proof.harness.BodyDecRef.
Require OpensslPunycode.proof.harness.RefA2u OpensslPunycode.proof.harness.BodyA2uRef.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require OpensslPunycode.proof.harness.a2ulabel.A2uMain.
Require Import OpensslPunycode.harness.x_a2ulabel.code.

Require Import OpensslPunycode.proof.harness.a2ulabel.A2uLawG.
Module L := OpensslPunycode.proof.libc.LibcSpec.
Module LB := OpensslPunycode.proof.libc.LibcBodies.
Module S := OpensslPunycode.proof.shim.ShimSpec.
Module SB := OpensslPunycode.proof.shim.ShimBodies.
Module K := OpensslPunycode.proof.packet.PacketSpec.
Module KB := OpensslPunycode.proof.packet.PacketBodies.
Module P := OpensslPunycode.proof.punycode.PunySpec.
Module PD := OpensslPunycode.proof.punycode.BodyDecode.
Module PA := OpensslPunycode.proof.punycode.BodyA2u.
Module R := OpensslPunycode.proof.harness.RefRt.
Module RB := OpensslPunycode.proof.harness.BodiesRt.
Module D := OpensslPunycode.proof.harness.RefDec.
Module DB := OpensslPunycode.proof.harness.BodyDecRef.
Module A := OpensslPunycode.proof.harness.RefA2u.
Module AB := OpensslPunycode.proof.harness.BodyA2uRef.


Lemma entries_G1 : Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G1.
Proof.
    entry_shared' (semax_body_main_std _ _ p _ _ OpensslPunycode.proof.harness.a2ulabel.A2uMain.body_main eq_refl).
    entry_shared' RB.body_copy_bytes.
    entry_shared' RB.body_same_bytes.
    entry_shared' AB.body_pr_a2ulabel.
    entry_shared' AB.body_pr_put.
    entry_shared' DB.body_pr_decode.
    entry_shared' DB.body_pr_digit_value.
    entry_shared' RB.body_pr_threshold.
    entry_shared' RB.body_pr_adapt.
    entry_shared' RB.body_pr_utf8.
    apply Forall_nil.
Qed.
