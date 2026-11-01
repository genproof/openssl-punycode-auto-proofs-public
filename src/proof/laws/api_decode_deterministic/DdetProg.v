(* The program of law api_decode_deterministic (harness/api_decode_deterministic.c), its compspecs and the context
   of its main, with the shared specifications of what main calls. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.contracts.api_decode_deterministic.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.

(* The law's program: the contract's whole_prog. *)
Definition p := OpensslPunycode.contracts.api_decode_deterministic.whole_prog.

(* The law's compspecs: the composites of its program. *)
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

(* What main calls. *)
Definition Gmain : funspecs :=
  [OpensslPunycode.proof.laws.common.HelperSpec.upto_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.any_bytes_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.copy_of_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.any_uints_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.uints_eq_spec;
   nondet_u32_spec; gp_assert_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_punycode_decode_spec].
