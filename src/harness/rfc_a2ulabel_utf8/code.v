From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "harness/rfc_a2ulabel_utf8.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _a : ident := $"a".
Definition _any_bytes : ident := $"any_bytes".
Definition _b : ident := $"b".
Definition _bytes : ident := $"bytes".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _c : ident := $"c".
Definition _copy : ident := $"copy".
Definition _copy_of : ident := $"copy_of".
Definition _count : ident := $"count".
Definition _cps : ident := $"cps".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _label : ident := $"label".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _o : ident := $"o".
Definition _ossl_a2ulabel : ident := $"ossl_a2ulabel".
Definition _ossl_punycode_decode : ident := $"ossl_punycode_decode".
Definition _ossl_shim_zalloc_failed : ident := $"ossl_shim_zalloc_failed".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _saved : ident := $"saved".
Definition _size : ident := $"size".
Definition _source : ident := $"source".
Definition _upto : ident := $"upto".
Definition _utf8 : ident := $"utf8".
Definition _valid : ident := $"valid".
Definition _value : ident := $"value".
Definition _want : ident := $"want".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_ossl_shim_zalloc_failed := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_upto := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_max, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _value (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _value tulong) (Etempvar _max tulong)
                   tint)
      (Sset _t'2 (Ecast (Etempvar _value tulong) tulong))
      (Sset _t'2 (Ecast (Etempvar _max tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_any_bytes := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bytes, (tptr tuchar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tulong) :: nil))
    (Sset _bytes (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _bytes (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Etempvar _bytes (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _bytes (tptr tuchar))))))
|}.

Definition f_copy_of := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_source, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_copy, (tptr tuchar)) :: (_i, tulong) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _source (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default))
        ((Etempvar _n tulong) :: nil))
      (Sset _copy (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _copy (tptr tuchar))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'2
                  (Ecast
                    (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                      tint) tbool))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _source (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _copy (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar)
                (Etempvar _t'3 tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Sreturn (Some (Etempvar _copy (tptr tuchar)))))))
|}.

Definition f_bytes_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
                  (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_utf8 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_c, tuint) :: (_o, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _c tuint)
                 (Econst_int (Int.repr 128) tint) tint)
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _o (tptr tuchar))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Etempvar _c tuint))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _c tuint)
                   (Econst_int (Int.repr 2048) tint) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _o (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oor (Econst_int (Int.repr 192) tint)
            (Ebinop Oshr (Etempvar _c tuint) (Econst_int (Int.repr 6) tint)
              tuint) tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
            (Ebinop Oor (Econst_int (Int.repr 128) tint)
              (Ebinop Oand (Etempvar _c tuint)
                (Econst_int (Int.repr 63) tint) tuint) tuint))
          (Sreturn (Some (Econst_int (Int.repr 2) tint)))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _c tuint)
                     (Econst_int (Int.repr 65536) tint) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Ebinop Oor (Econst_int (Int.repr 224) tint)
              (Ebinop Oshr (Etempvar _c tuint)
                (Econst_int (Int.repr 12) tint) tuint) tuint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Ebinop Oor (Econst_int (Int.repr 128) tint)
                (Ebinop Oand
                  (Ebinop Oshr (Etempvar _c tuint)
                    (Econst_int (Int.repr 6) tint) tuint)
                  (Econst_int (Int.repr 63) tint) tuint) tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                (Ebinop Oor (Econst_int (Int.repr 128) tint)
                  (Ebinop Oand (Etempvar _c tuint)
                    (Econst_int (Int.repr 63) tint) tuint) tuint))
              (Sreturn (Some (Econst_int (Int.repr 3) tint))))))
        Sskip)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _o (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oor (Econst_int (Int.repr 240) tint)
            (Ebinop Oshr (Etempvar _c tuint) (Econst_int (Int.repr 18) tint)
              tuint) tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
            (Ebinop Oor (Econst_int (Int.repr 128) tint)
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _c tuint)
                  (Econst_int (Int.repr 12) tint) tuint)
                (Econst_int (Int.repr 63) tint) tuint) tuint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
              (Ebinop Oor (Econst_int (Int.repr 128) tint)
                (Ebinop Oand
                  (Ebinop Oshr (Etempvar _c tuint)
                    (Econst_int (Int.repr 6) tint) tuint)
                  (Econst_int (Int.repr 63) tint) tuint) tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                (Ebinop Oor (Econst_int (Int.repr 128) tint)
                  (Ebinop Oand (Etempvar _c tuint)
                    (Econst_int (Int.repr 63) tint) tuint) tuint))
              (Sreturn (Some (Econst_int (Int.repr 4) tint))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_count, tuint) :: nil);
  fn_temps := ((_len, tulong) :: (_label, (tptr tuchar)) ::
               (_cps, (tptr tuint)) :: (_outlen, tulong) ::
               (_out, (tptr tuchar)) :: (_saved, (tptr tuchar)) ::
               (_want, (tptr tuchar)) :: (_i, tulong) :: (_valid, tint) ::
               (_size, tulong) :: (_j, tuint) :: (_r, tint) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tulong) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tuchar)) :: (_t'5, (tptr tuchar)) ::
               (_t'4, tulong) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tuchar)) :: (_t'1, tulong) :: (_t'27, tuchar) ::
               (_t'26, tuchar) :: (_t'25, tuint) :: (_t'24, tuint) ::
               (_t'23, tuint) :: (_t'22, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
        ((Ebinop Osub (Econst_long (Int64.repr 9223372036854775807) tlong)
           (Econst_int (Int.repr 5) tint) tlong) :: nil))
      (Sset _len (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                             cc_default))
          ((Ebinop Oadd (Etempvar _len tulong) (Econst_int (Int.repr 5) tint)
             tulong) :: nil))
        (Sset _label (Etempvar _t'2 (tptr tuchar))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                       cc_default))
            ((Ebinop Omul (Econst_int (Int.repr 512) tint)
               (Esizeof tuint tulong) tulong) :: nil))
          (Sset _cps (Etempvar _t'3 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
              ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
            (Sset _outlen (Etempvar _t'4 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                                   cc_default))
                ((Etempvar _outlen tulong) :: nil))
              (Sset _out (Etempvar _t'5 (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _copy_of (Tfunction ((tptr tuchar) :: tulong :: nil)
                                   (tptr tuchar) cc_default))
                  ((Etempvar _out (tptr tuchar)) ::
                   (Etempvar _outlen tulong) :: nil))
                (Sset _saved (Etempvar _t'6 (tptr tuchar))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                               (tptr tvoid) cc_default))
                    ((Ebinop Oadd
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                         (Econst_int (Int.repr 512) tint) tint)
                       (Econst_int (Int.repr 1) tint) tint) :: nil))
                  (Sset _want (Etempvar _t'7 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _label (tptr tuchar))
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) tint)
                              (Sset _t'8 (Econst_int (Int.repr 1) tint))
                              (Sset _t'8
                                (Ecast
                                  (Ebinop Oeq (Etempvar _cps (tptr tuint))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) tint) tbool)))
                            (Sifthenelse (Etempvar _t'8 tint)
                              (Sset _t'9 (Econst_int (Int.repr 1) tint))
                              (Sset _t'9
                                (Ecast
                                  (Ebinop Oeq (Etempvar _out (tptr tuchar))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) tint) tbool))))
                          (Sifthenelse (Etempvar _t'9 tint)
                            (Sset _t'10 (Econst_int (Int.repr 1) tint))
                            (Sset _t'10
                              (Ecast
                                (Ebinop Oeq (Etempvar _saved (tptr tuchar))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)) tint) tbool))))
                        (Sifthenelse (Etempvar _t'10 tint)
                          (Sset _t'11 (Econst_int (Int.repr 1) tint))
                          (Sset _t'11
                            (Ecast
                              (Ebinop Oeq (Etempvar _want (tptr tuchar))
                                (Ecast (Econst_int (Int.repr 0) tint)
                                  (tptr tvoid)) tint) tbool))))
                      (Sifthenelse (Etempvar _t'11 tint)
                        (Sset _t'12 (Econst_int (Int.repr 1) tint))
                        (Sset _t'12
                          (Ecast
                            (Ebinop Oeq (Etempvar _outlen tulong)
                              (Econst_int (Int.repr 0) tint) tint) tbool))))
                    (Sifthenelse (Etempvar _t'12 tint)
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                      Sskip))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _label (tptr tuchar))
                          (Econst_int (Int.repr 0) tint) (tptr tuchar))
                        tuchar) (Econst_int (Int.repr 120) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _label (tptr tuchar))
                            (Econst_int (Int.repr 1) tint) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 110) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _label (tptr tuchar))
                              (Econst_int (Int.repr 2) tint) (tptr tuchar))
                            tuchar) (Econst_int (Int.repr 45) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _label (tptr tuchar))
                                (Econst_int (Int.repr 3) tint) (tptr tuchar))
                              tuchar) (Econst_int (Int.repr 45) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _label (tptr tuchar))
                                  (Ebinop Oadd (Etempvar _len tulong)
                                    (Econst_int (Int.repr 4) tint) tulong)
                                  (tptr tuchar)) tuchar)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ecast (Econst_int (Int.repr 4) tint)
                                    tulong))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tulong)
                                                   (Ebinop Oadd
                                                     (Etempvar _len tulong)
                                                     (Econst_int (Int.repr 4) tint)
                                                     tulong) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'26
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _label (tptr tuchar))
                                              (Etempvar _i tulong)
                                              (tptr tuchar)) tuchar))
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar _t'26 tuchar)
                                                       (Econst_int (Int.repr 46) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _t'27
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _label (tptr tuchar))
                                                  (Etempvar _i tulong)
                                                  (tptr tuchar)) tuchar))
                                            (Sset _t'13
                                              (Ecast
                                                (Ebinop One
                                                  (Etempvar _t'27 tuchar)
                                                  (Econst_int (Int.repr 0) tint)
                                                  tint) tbool)))
                                          (Sset _t'13
                                            (Econst_int (Int.repr 0) tint))))
                                      (Scall None
                                        (Evar _gp_assume (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Etempvar _t'13 tint) :: nil))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tulong)
                                      (Econst_int (Int.repr 1) tint) tulong))))
                              (Ssequence
                                (Sassign (Evar _count tuint)
                                  (Econst_int (Int.repr 512) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'14)
                                      (Evar _ossl_punycode_decode (Tfunction
                                                                    ((tptr tschar) ::
                                                                    tulong ::
                                                                    (tptr tuint) ::
                                                                    (tptr tuint) ::
                                                                    nil) tint
                                                                    cc_default))
                                      ((Ebinop Oadd
                                         (Ecast
                                           (Etempvar _label (tptr tuchar))
                                           (tptr tschar))
                                         (Econst_int (Int.repr 4) tint)
                                         (tptr tschar)) ::
                                       (Etempvar _len tulong) ::
                                       (Etempvar _cps (tptr tuint)) ::
                                       (Eaddrof (Evar _count tuint)
                                         (tptr tuint)) :: nil))
                                    (Sset _valid
                                      (Ebinop Oeq (Etempvar _t'14 tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  (Ssequence
                                    (Sset _size
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tulong))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _j
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Etempvar _valid tint)
                                                (Ssequence
                                                  (Sset _t'25
                                                    (Evar _count tuint))
                                                  (Sset _t'15
                                                    (Ecast
                                                      (Ebinop Olt
                                                        (Etempvar _j tuint)
                                                        (Etempvar _t'25 tuint)
                                                        tint) tbool)))
                                                (Sset _t'15
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _t'15 tint)
                                                Sskip
                                                Sbreak))
                                            (Ssequence
                                              (Sset _t'23
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _cps (tptr tuint))
                                                    (Etempvar _j tuint)
                                                    (tptr tuint)) tuint))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _t'23 tuint)
                                                             (Econst_int (Int.repr 1114111) tint)
                                                             tint)
                                                (Sset _valid
                                                  (Econst_int (Int.repr 0) tint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'24
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _cps (tptr tuint))
                                                          (Etempvar _j tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'16)
                                                      (Evar _utf8 (Tfunction
                                                                    (tuint ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                      ((Etempvar _t'24 tuint) ::
                                                       (Ebinop Oadd
                                                         (Etempvar _want (tptr tuchar))
                                                         (Etempvar _size tulong)
                                                         (tptr tuchar)) ::
                                                       nil)))
                                                  (Sset _size
                                                    (Ebinop Oadd
                                                      (Etempvar _size tulong)
                                                      (Etempvar _t'16 tulong)
                                                      tulong))))))
                                          (Sset _j
                                            (Ebinop Oadd (Etempvar _j tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _want (tptr tuchar))
                                              (Etempvar _size tulong)
                                              (tptr tuchar)) tuchar)
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sset _size
                                            (Ebinop Oadd
                                              (Etempvar _size tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong))
                                          (Ssequence
                                            (Sassign
                                              (Evar _ossl_shim_zalloc_failed tint)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'17)
                                                  (Evar _ossl_a2ulabel 
                                                  (Tfunction
                                                    ((tptr tschar) ::
                                                     (tptr tschar) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                                                  ((Ecast
                                                     (Etempvar _label (tptr tuchar))
                                                     (tptr tschar)) ::
                                                   (Ecast
                                                     (Etempvar _out (tptr tuchar))
                                                     (tptr tschar)) ::
                                                   (Etempvar _outlen tulong) ::
                                                   nil))
                                                (Sset _r
                                                  (Etempvar _t'17 tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'22
                                                    (Evar _ossl_shim_zalloc_failed tint))
                                                  (Sifthenelse (Etempvar _t'22 tint)
                                                    (Scall None
                                                      (Evar _gp_assert 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Ebinop Oeq
                                                         (Etempvar _r tint)
                                                         (Eunop Oneg
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint) tint) ::
                                                       nil))
                                                    (Sifthenelse (Eunop Onotbool
                                                                   (Etempvar _valid tint)
                                                                   tint)
                                                      (Scall None
                                                        (Evar _gp_assert 
                                                        (Tfunction
                                                          (tint :: nil) tvoid
                                                          cc_default))
                                                        ((Ebinop Oeq
                                                           (Etempvar _r tint)
                                                           (Eunop Oneg
                                                             (Econst_int (Int.repr 1) tint)
                                                             tint) tint) ::
                                                         nil))
                                                      (Sifthenelse (Ebinop Ole
                                                                    (Etempvar _size tulong)
                                                                    (Etempvar _outlen tulong)
                                                                    tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _r tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Scall (Some _t'19)
                                                                  (Evar _bytes_eq 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                  ((Etempvar _out (tptr tuchar)) ::
                                                                   (Etempvar _want (tptr tuchar)) ::
                                                                   (Etempvar _size tulong) ::
                                                                   nil))
                                                                (Sset _t'18
                                                                  (Ecast
                                                                    (Etempvar _t'19 tint)
                                                                    tbool)))
                                                              (Sset _t'18
                                                                (Econst_int (Int.repr 0) tint)))
                                                            (Sifthenelse (Etempvar _t'18 tint)
                                                              (Ssequence
                                                                (Scall (Some _t'21)
                                                                  (Evar _bytes_eq 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                  ((Ebinop Oadd
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _size tulong)
                                                                    (tptr tuchar)) ::
                                                                   (Ebinop Oadd
                                                                    (Etempvar _saved (tptr tuchar))
                                                                    (Etempvar _size tulong)
                                                                    (tptr tuchar)) ::
                                                                   (Ebinop Osub
                                                                    (Etempvar _outlen tulong)
                                                                    (Etempvar _size tulong)
                                                                    tulong) ::
                                                                   nil))
                                                                (Sset _t'20
                                                                  (Ecast
                                                                    (Etempvar _t'21 tint)
                                                                    tbool)))
                                                              (Sset _t'20
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Scall None
                                                            (Evar _gp_assert 
                                                            (Tfunction
                                                              (tint :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _t'20 tint) ::
                                                             nil)))
                                                        (Scall None
                                                          (Evar _gp_assert 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Ebinop Oeq
                                                             (Etempvar _r tint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint) :: nil))))))
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_gp_assume,
   Gfun(External (EF_external "gp_assume"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_ossl_punycode_decode,
   Gfun(External (EF_external "ossl_punycode_decode"
                   (mksignature
                     (AST.Xptr :: AST.Xlong :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tschar) :: tulong :: (tptr tuint) :: (tptr tuint) :: nil) tint
     cc_default)) ::
 (_ossl_a2ulabel,
   Gfun(External (EF_external "ossl_a2ulabel"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr tschar) :: (tptr tschar) :: tulong :: nil) tint cc_default)) ::
 (_ossl_shim_zalloc_failed, Gvar v_ossl_shim_zalloc_failed) ::
 (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_copy_of, Gfun(Internal f_copy_of)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) :: (_utf8, Gfun(Internal f_utf8)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ossl_shim_zalloc_failed :: _ossl_a2ulabel ::
 _ossl_punycode_decode :: _gp_assume :: _gp_assert :: _nondet_bytes ::
 _nondet_size :: _quickproof_malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


