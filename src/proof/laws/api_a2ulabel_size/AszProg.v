(* Law api_a2ulabel_size: its program (the contract's whole_prog), its compspecs and the context of its main
   (harness/api_a2ulabel_size.c), with the shared specifications of what main calls. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.contracts.api_a2ulabel_size.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.

Definition p := OpensslPunycode.contracts.api_a2ulabel_size.whole_prog.

(* The law's compspecs: the composites of its program. *)
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

(* What main calls. *)
Definition Gmain : funspecs :=
  [nondet_size_spec; gp_assert_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.upto_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.any_bytes_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.bytes_eq_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_a2ulabel_spec].
