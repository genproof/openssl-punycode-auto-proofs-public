(* The specifications of the framework's libc functions that the laws reach (quickproof/libc/libc.c): memcpy, memset.
   Under the unit's compspecs (OpensslPunycode.units.Libc.CS). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.units.Libc.
Require Import OpensslPunycode.libc.code.

#[export] Instance CS : compspecs := OpensslPunycode.units.Libc.CS.
Definition Vprog : varspecs. mk_varspecs OpensslPunycode.libc.code.prog. Defined.

(* memcpy(d, s, n): the n octets l of s are copied to d (disjoint arrays; n = 0: nothing, any pointers). *)
Definition memcpy_spec :=
  DECLARE _memcpy
  WITH shd: share, d: val, dold: list val, shs: share, s: val, l: list Z
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (writable_share shd; readable_share shs; bytes_ok l; Zlength dold = Zlength l;
          Zlength l <= Int64.max_unsigned)
    PARAMS (d; s; Vlong (Int64.repr (Zlength l)))
    SEP (arr0 shd tuchar (Zlength l) dold d; arr0 shs tuchar (Zlength l) (vb l) s)
  POST [ tptr tvoid ]
    PROP () RETURN (d)
    SEP (arr0 shd tuchar (Zlength l) (vb l) d; arr0 shs tuchar (Zlength l) (vb l) s).

(* memset(p, c, n): the n octets of p become (unsigned char) c. *)
Definition memset_spec :=
  DECLARE _memset
  WITH sh: share, p: val, old: list val, c: Z, n: Z
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; Int.min_signed <= c <= Int.max_signed; 0 <= n <= Int64.max_unsigned;
          Zlength old = n)
    PARAMS (p; Vint (Int.repr c); Vlong (Int64.repr n))
    SEP (arr0 sh tuchar n old p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (arr0 sh tuchar n (Zrepeat (Vint (Int.repr (c mod 256))) n) p).

Definition Gprog : funspecs := [memcpy_spec; memset_spec].
