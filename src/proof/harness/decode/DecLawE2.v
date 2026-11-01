(* Law decode: the entries of G2 (the code under test and the environment). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Asm.
Require OpensslPunycode.proof.punycode.BodyDecode.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecLawG.

Module PD := OpensslPunycode.proof.punycode.BodyDecode.

Lemma entries_G2 : Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G2.
Proof.
    entry_shared' PD.body_ossl_punycode_decode.
    entry_shared' PD.body_adapt.
    entry_shared' PD.body_is_basic.
    entry_shared' PD.body_digit_decoded.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
