(* Law a2ulabel: the entries of G2 (the code under test and the environment). *)
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


Lemma entries_G2 : Forall (entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)) G2.
Proof.
    entry_shared' PA.body_ossl_a2ulabel.
    entry_shared' PA.body_codepoint2utf8.
    entry_shared' PD.body_ossl_punycode_decode.
    entry_shared' PD.body_adapt.
    entry_shared' PD.body_is_basic.
    entry_shared' PD.body_digit_decoded.
    entry_shared' SB.body_strchr.
    entry_shared' SB.body_strlen.
    entry_shared' SB.body_OPENSSL_strncasecmp.
    entry_shared' SB.body_shim_tolower.
    entry_shared' SB.body_CRYPTO_zalloc.
    entry_shared' SB.body_CRYPTO_free.
    entry_shared' KB.body_WPACKET_init_static_len.
    entry_shared' KB.body_maxmaxsize.
    entry_shared' KB.body_wpacket_intern_init_len.
    entry_shared' KB.body_WPACKET_memcpy.
    entry_shared' KB.body_WPACKET_put_bytes__.
    entry_shared' KB.body_put_value.
    entry_shared' KB.body_WPACKET_allocate_bytes.
    entry_shared' KB.body_WPACKET_reserve_bytes.
    entry_shared' KB.body_WPACKET_get_curr.
    entry_shared' KB.body_WPACKET_cleanup.
    entry_shared' LB.body_memcpy.
    entry_shared' LB.body_memset.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
