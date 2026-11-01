(* The program of law roundtrip, its compspecs and the context of its main (harness/x_roundtrip.c), under the law's compspecs, with the shared specifications
   of what it calls, from the model's roundtrip theorem (OpensslPunycode.proof.model.Roundtrip, as hypotheses).
  *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require OpensslPunycode.units.Punycode.
Require OpensslPunycode.units.Packet.
Require OpensslPunycode.units.Shim.
Require OpensslPunycode.units.Libc.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

(* The law's program, computed exactly as src/contracts/roundtrip.v computes whole_prog (this module cannot
   Require the contract, which Requires it): the two are the same term. *)
Module Harness.
  #[local] Instance CS : compspecs. make_compspecs OpensslPunycode.harness.x_roundtrip.code.prog. Defined.
  Definition qp := ltac:(QPprog OpensslPunycode.harness.x_roundtrip.code.prog).
End Harness.
Definition link_Packet := ltac:(QPlink_progs Packet.qp Punycode.qp).
Definition link_Shim := ltac:(QPlink_progs Shim.qp link_Packet).
Definition link_Libc := ltac:(QPlink_progs Libc.qp link_Shim).
Definition p := ltac:(QPlink_progs Harness.qp link_Libc).

(* The law's compspecs: the composites of its program. *)
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

(* What main calls. *)
Definition Gmain : funspecs :=
  [nondet_size_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec;
   (_quickproof_malloc, malloc_spec');
   OpensslPunycode.proof.harness.RefRt.pr_encode_spec; OpensslPunycode.proof.harness.RefRt.pr_utf8_spec;
   OpensslPunycode.proof.harness.RefRt.copy_bytes_spec; OpensslPunycode.proof.harness.RefRt.same_bytes_spec;
   OpensslPunycode.proof.harness.RefRt.same_uints_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_punycode_decode_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_a2ulabel_spec].
