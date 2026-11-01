(* The specifications of the harness's own functions of law rt_roundtrip (harness/rt_roundtrip.c): rfc_adapt, put,
   digit and the RFC 3492 encoder encode, which computes Model.encode exactly; and the context of its main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Local Open Scope logic.

(* rfc_adapt(delta, numpoints, firsttime): RFC 3492 6.1, Model.adapt. *)
Definition rfc_adapt_spec :=
  DECLARE _rfc_adapt
  WITH delta: Z, numpoints: Z, firsttime: Z
  PRE [ tulong, tulong, tint ]
    PROP (0 <= delta <= maxint; 1 <= numpoints <= Int64.max_unsigned; Int.min_signed <= firsttime <= Int.max_signed)
    PARAMS (Vlong (Int64.repr delta); Vlong (Int64.repr numpoints); Vint (Int.repr firsttime))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (adapt delta numpoints (negb (firsttime =? 0))))) SEP ().

(* digit(d): the lowercase octet of the digit-value d < 36 (Model.digit_char). *)
Definition digit_spec :=
  DECLARE _digit
  WITH d: Z
  PRE [ tulong ]
    PROP (0 <= d < 36) PARAMS (Vlong (Int64.repr d)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (digit_char d))) SEP ().

(* put(out, room, len, c): when *len < room, the octet c at out[*len] and *len + 1 (result 1); else nothing
   changes (result 0).  c is an octet: every caller writes a basic code point, '-' or a digit. *)
Definition put_spec :=
  DECLARE _put
  WITH sh: share, po: val, room: Z, buf: list val, shl: share, pl: val, l: Z, c: Z
  PRE [ tptr tuchar, tulong, tptr tulong, tulong ]
    PROP (writable_share sh; writable_share shl; 0 <= l <= room; room <= Int64.max_unsigned;
          Zlength buf = room; 0 <= c <= Byte.max_unsigned)
    PARAMS (po; Vlong (Int64.repr room); pl; Vlong (Int64.repr c))
    SEP (arr0 sh tuchar room buf po; data_at shl tulong (Vlong (Int64.repr l)) pl)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if l <? room then 1 else 0)))
    SEP (arr0 sh tuchar room (if l <? room then upd_Znth l buf (Vint (Int.repr c)) else buf) po;
         data_at shl tulong (Vlong (Int64.repr (if l <? room then l + 1 else l))) pl).

(* encode(cps, m, out, room, len): RFC 3492 6.3 in 64-bit arithmetic.  Result 1 exactly when Model.encode cps is
   Some e with |e| <= room; then out holds e followed by its other octets and *len = |e|.  Result 0 otherwise (an
   overflow, or the encoding does not fit), with out and *len holding anything.  Any number of code points, each
   any unsigned int (RefRt.encode_fits, encode_out, encode_len: the same outcome as pr_encode's). *)
Definition encode_spec :=
  DECLARE _encode
  WITH shc: share, pc: val, cps: list Z, sho: share, po: val, room: Z, oinit: list val, shl: share, pl: val
  PRE [ tptr tuint, tulong, tptr tuchar, tulong, tptr tulong ]
    PROP (readable_share shc; writable_share sho; writable_share shl;
          Forall (fun c => 0 <= c <= Int.max_unsigned) cps; 4 * Zlength cps <= Int64.max_unsigned;
          0 <= room <= Int64.max_unsigned; Zlength oinit = room)
    PARAMS (pc; Vlong (Int64.repr (Zlength cps)); po; Vlong (Int64.repr room); pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room oinit po; data_at_ shl tulong pl)
  POST [ tint ]
    EX o': list val,
    PROP (Zlength o' = room)
    RETURN (Vint (Int.repr (if RefRt.encode_fits cps room then 1 else 0)))
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (RefRt.encode_out cps room oinit o') po;
         if RefRt.encode_fits cps room then data_at shl tulong (Vlong (Int64.repr (RefRt.encode_len cps))) pl
         else data_at_ shl tulong pl).

Module C := OpensslPunycode.proof.laws.common.HelperSpec.

(* The contexts: what encode calls, what the leaf functions call, what main calls. *)
Definition Vprog : varspecs := [].
Definition Gprog_encode : funspecs := [put_spec; digit_spec; rfc_adapt_spec].
Definition Gprog_none : funspecs := [].
Definition Gmain : funspecs :=
  [C.upto_spec; C.any_uints_spec; (_quickproof_malloc, malloc_spec'); encode_spec;
   OpensslPunycode.proof.punycode.PunySpec.ossl_punycode_decode_spec; gp_assert_spec; C.uints_eq_spec].
