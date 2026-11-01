(* Law a2ulabel: the context G of the law (main, the harness's functions, the code under test, the environment). *)
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

(* main, the functions it reaches with their callees, the environment it calls: G1 = main and the harness's own
   functions, G2 = the code under test and the environment. *)
Definition G1 : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   R.copy_bytes_spec; R.same_bytes_spec; A.pr_a2ulabel_spec; A.pr_put_spec; D.pr_decode_spec;
   D.pr_digit_value_spec; R.pr_threshold_spec; R.pr_adapt_spec; R.pr_utf8_spec].
Definition G2 : funspecs :=
  [P.ossl_a2ulabel_spec; P.codepoint2utf8_spec; P.ossl_punycode_decode_spec; P.adapt_spec; P.is_basic_spec;
   P.digit_decoded_spec;
   S.strchr_spec; S.strlen_spec; S.OPENSSL_strncasecmp_spec; S.shim_tolower_spec; S.CRYPTO_zalloc_spec;
   S.CRYPTO_free_spec;
   K.WPACKET_init_static_len_spec; K.maxmaxsize_spec; K.wpacket_intern_init_len_spec; K.WPACKET_memcpy_spec;
   K.WPACKET_put_bytes___spec; K.put_value_spec; K.WPACKET_allocate_bytes_spec; K.WPACKET_reserve_bytes_spec;
   K.WPACKET_get_curr_spec; K.WPACKET_cleanup_spec;
   L.memcpy_spec; L.memset_spec;
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; nondet_u8_spec; @nondet_bytes_spec CS; gp_assert_spec; gp_assume_spec].
Definition G : funspecs := G1 ++ G2.
