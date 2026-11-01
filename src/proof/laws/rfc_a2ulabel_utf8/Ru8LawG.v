(* Law rfc_a2ulabel_utf8: the context G of the law (main, the helpers of laws_common.h it calls, the code under test,
   the environment). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.libc.LibcSpec.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.

Module L := OpensslPunycode.proof.libc.LibcSpec.
Module S := OpensslPunycode.proof.shim.ShimSpec.
Module K := OpensslPunycode.proof.packet.PacketSpec.
Module P := OpensslPunycode.proof.punycode.PunySpec.
Module C := OpensslPunycode.proof.laws.common.HelperSpec.

(* G1 = main and the harness's own functions, G2 = the code under test and the environment. *)
Definition G1 : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   C.upto_spec; C.any_bytes_spec; C.copy_of_spec; C.bytes_eq_spec; utf8_spec].
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
   nondet_size_spec; @nondet_bytes_spec CS; gp_assert_spec; gp_assume_spec].
Definition G : funspecs := G1 ++ G2.
