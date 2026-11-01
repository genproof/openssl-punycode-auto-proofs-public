(* Law rfc_a2ulabel_utf8: its program (the contract's whole_prog), its compspecs, the specification of the harness's
   own function utf8 (harness/rfc_a2ulabel_utf8.c), and the context of its main, with the shared specifications of
   what main calls. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.contracts.rfc_a2ulabel_utf8.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.

Definition p := OpensslPunycode.contracts.rfc_a2ulabel_utf8.whole_prog.

(* The law's compspecs: the composites of its program. *)
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

(* utf8(c, o) of the harness, for a code point c <= 0x10FFFF: the UTF-8 octets of c (Model.utf8, RFC 3629) at o,
   which has room for exactly them, and their number. *)
Definition utf8_spec :=
  DECLARE _utf8
  WITH c: Z, sh: share, o: val, old: list val
  PRE [ tuint, tptr tuchar ]
    PROP (writable_share sh; 0 <= c <= 1114111; Zlength old = Zlength (utf8 c))
    PARAMS (Vint (Int.repr c); o)
    SEP (data_at sh (tarray tuchar (Zlength (utf8 c))) old o)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Zlength (utf8 c))))
    SEP (data_at sh (tarray tuchar (Zlength (utf8 c))) (vb (utf8 c)) o).

(* What main calls. *)
Definition Gmain : funspecs :=
  [gp_assert_spec; gp_assume_spec; (_quickproof_malloc, @malloc_spec' CS);
   OpensslPunycode.proof.laws.common.HelperSpec.upto_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.any_bytes_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.copy_of_spec;
   OpensslPunycode.proof.laws.common.HelperSpec.bytes_eq_spec;
   utf8_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_punycode_decode_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_a2ulabel_spec].
