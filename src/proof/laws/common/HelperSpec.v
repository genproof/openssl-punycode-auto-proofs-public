(* The specifications of the helpers of harness/laws_common.h (upto, any_bytes, any_uints, copy_of, bytes_eq,
   uints_eq, last_delimiter), shared by every short law; their bodies are proved in Cmn*.v of this directory.  Each
   harness has its own copy of these static functions, with the same Clight body (the identifiers are the `$"name"`
   identifiers of every unit) and no composites, so a body proved once here, under the compspecs of
   harness/rfc_digit_case.c, moves to every law (entry_shared' of src/proof/common/Asm.v).  bytes_eq is not in
   rfc_digit_case.c: its Clight is taken from harness/rj_decode_any.c.  Each body is proved under the context of
   exactly the functions it calls, so that it moves to a law whose program has only those.

   No size is bounded by a constant: every length is any size_t (the count of any_uints' elements times 4 within
   size_t), every array has the length the allocator gave it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.harness.rj_decode_any.code.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

#[export] Instance CS : compspecs. make_compspecs OpensslPunycode.harness.rfc_digit_case.code.prog. Defined.
Local Open Scope logic.

(* upto(max): any value from 0 to max. *)
Definition upto_spec :=
  DECLARE _upto
  WITH max: Z
  PRE [ tulong ]
    PROP (0 <= max <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr max))
    SEP ()
  POST [ tulong ]
    EX v: Z,
    PROP (0 <= v <= max)
    RETURN (Vlong (Int64.repr v))
    SEP ().

(* any_bytes(n): NULL (malloc failed), or a new block of n arbitrary octets with its malloc token. *)
Definition any_bytes_spec :=
  DECLARE _any_bytes
  WITH n: Z, gv: globals
  PRE [ tulong ]
    PROP (0 <= n <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuchar ]
    EX p: val, EX bs: list Z,
    PROP (Zlength bs = n; bytes_ok bs)
    RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (vb bs) p).

(* any_uints(n): NULL (malloc failed), or a new block of n arbitrary unsigned ints with its malloc token. *)
Definition any_uints_spec :=
  DECLARE _any_uints
  WITH n: Z, gv: globals
  PRE [ tulong ]
    PROP (0 <= n; 4 * n <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuint ]
    EX p: val, EX vs: list Z,
    PROP (Zlength vs = n; Forall (fun x => 0 <= x <= Int.max_unsigned) vs)
    RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuint n) p * data_at Ews (tarray tuint n) (vb vs) p).

(* copy_of(source, n): NULL when source is NULL or malloc fails, else a new block holding the first n octets of
   source.  The source is a block that malloc gave (its token and its octets bs, n <= |bs|): the test
   `source == NULL` is defined only for a valid pointer, which the token witnesses when the block is empty. *)
Definition copy_of_spec :=
  DECLARE _copy_of
  WITH sh: share, src: val, bs: list Z, n: Z, gv: globals
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; bytes_ok bs; 0 <= n <= Zlength bs; Zlength bs <= Int64.max_unsigned)
    PARAMS (src; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; if eq_dec src nullval then emp
         else malloc_token Ews (tarray tuchar (Zlength bs)) src * data_at sh (tarray tuchar (Zlength bs)) (vb bs) src)
  POST [ tptr tuchar ]
    EX p: val,
    PROP (src = nullval -> p = nullval)
    RETURN (p)
    SEP (mem_mgr gv; if eq_dec src nullval then emp
         else malloc_token Ews (tarray tuchar (Zlength bs)) src * data_at sh (tarray tuchar (Zlength bs)) (vb bs) src;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (vb (sublist 0 n bs)) p).

(* bytes_eq(a, b, n): 1 when the n octets at a and at b are equal, else 0. *)
Definition bytes_eq_spec :=
  DECLARE OpensslPunycode.harness.rj_decode_any.code._bytes_eq
  WITH sha: share, a: val, la: list Z, shb: share, b: val, lb: list Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; bytes_ok la; bytes_ok lb; Zlength la = Zlength lb;
          Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (arr0 sha tuchar (Zlength la) (vb la) a; arr0 shb tuchar (Zlength la) (vb lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec la lb then 1 else 0)))
    SEP (arr0 sha tuchar (Zlength la) (vb la) a; arr0 shb tuchar (Zlength la) (vb lb) b).

(* uints_eq(a, b, n): 1 when the n unsigned ints at a and at b are equal, else 0. *)
Definition uints_eq_spec :=
  DECLARE _uints_eq
  WITH sha: share, a: val, la: list Z, shb: share, b: val, lb: list Z
  PRE [ tptr tuint, tptr tuint, tulong ]
    PROP (readable_share sha; readable_share shb; Forall (fun x => 0 <= x <= Int.max_unsigned) la;
          Forall (fun x => 0 <= x <= Int.max_unsigned) lb; Zlength la = Zlength lb;
          Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (arr0 sha tuint (Zlength la) (vb la) a; arr0 shb tuint (Zlength la) (vb lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec la lb then 1 else 0)))
    SEP (arr0 sha tuint (Zlength la) (vb la) a; arr0 shb tuint (Zlength la) (vb lb) b).

(* last_delimiter(s, n): the position of the last '-' of the n octets at s, 0 if none (Model.last_delim). *)
Definition last_delimiter_spec :=
  DECLARE _last_delimiter
  WITH sh: share, s: val, l: list Z
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; bytes_ok l; Zlength l <= Int64.max_unsigned)
    PARAMS (s; Vlong (Int64.repr (Zlength l)))
    SEP (arr0 sh tuchar (Zlength l) (vb l) s)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (last_delim l)))
    SEP (arr0 sh tuchar (Zlength l) (vb l) s).

(* The callees of each helper (Vprog: none of them reads a global). *)
Definition Vprog : varspecs := [].
Definition Gprog_upto : funspecs := [nondet_size_spec].
Definition Gprog_any_bytes : funspecs := [nondet_bytes_spec; (_quickproof_malloc, malloc_spec')].
Definition Gprog_any_uints : funspecs := [nondet_u32_spec; (_quickproof_malloc, malloc_spec')].
Definition Gprog_copy_of : funspecs := [(_quickproof_malloc, malloc_spec')].
Definition Gprog_none : funspecs := [].
