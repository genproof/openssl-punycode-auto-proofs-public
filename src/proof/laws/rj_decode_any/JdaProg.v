(* The program of law rj_decode_any (harness/rj_decode_any.c), its compspecs and the context of its main: the helpers
   of harness/laws_common.h it calls (src/proof/laws/common/HelperSpec.v), ossl_punycode_decode
   (src/proof/punycode/PunySpec.v) and the environment. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.contracts.rj_decode_any.

(* The law's program: the contract's whole_prog. *)
Definition p := OpensslPunycode.contracts.rj_decode_any.whole_prog.

(* The law's compspecs: the composites of its program. *)
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

Module C := OpensslPunycode.proof.laws.common.HelperSpec.

(* What main calls. *)
Definition Gmain : funspecs :=
  [C.upto_spec; C.any_bytes_spec; C.copy_of_spec; nondet_u32_spec; C.any_uints_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_punycode_decode_spec; gp_assert_spec; C.bytes_eq_spec].
