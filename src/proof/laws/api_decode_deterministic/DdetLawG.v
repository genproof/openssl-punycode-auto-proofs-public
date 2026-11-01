(* Law api_decode_deterministic: the context G of the law (main, the helpers of laws_common.h it calls, the code
   under test, the environment). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.

Module P := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

(* G1 = main and the harness's own functions, G2 = the code under test and the environment. *)
Definition G1 : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   CM.upto_spec; CM.any_bytes_spec; CM.copy_of_spec; CM.any_uints_spec; CM.uints_eq_spec].
Definition G2 : funspecs :=
  [P.ossl_punycode_decode_spec; P.adapt_spec; P.is_basic_spec; P.digit_decoded_spec;
   (_quickproof_malloc, @malloc_spec' CS); nondet_size_spec; nondet_u32_spec; @nondet_bytes_spec CS;
   gp_assert_spec].
Definition G : funspecs := G1 ++ G2.
