(* Law decode: the context G of the law (main, the harness's functions, the code under test, the environment). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.harness.x_decode.code.

Module P := OpensslPunycode.proof.punycode.PunySpec.
Module R := OpensslPunycode.proof.harness.RefRt.
Module D := OpensslPunycode.proof.harness.RefDec.

(* G1 = main and the harness's own functions, G2 = the code under test and the environment. *)
Definition G1 : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   R.copy_bytes_spec; R.same_bytes_spec; R.same_uints_spec; D.pr_decode_spec; D.pr_digit_value_spec;
   R.pr_threshold_spec; R.pr_adapt_spec].
Definition G2 : funspecs :=
  [P.ossl_punycode_decode_spec; P.adapt_spec; P.is_basic_spec; P.digit_decoded_spec;
   (_quickproof_malloc, @malloc_spec' CS); nondet_size_spec; @nondet_bytes_spec CS; gp_assert_spec].
Definition G : funspecs := G1 ++ G2.
