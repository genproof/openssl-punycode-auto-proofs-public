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
  Definition source_file := "harness/rt_roundtrip.c".
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
Definition _any_uints : ident := $"any_uints".
Definition _b : ident := $"b".
Definition _bias : ident := $"bias".
Definition _c : ident := $"c".
Definition _count : ident := $"count".
Definition _cps : ident := $"cps".
Definition _d : ident := $"d".
Definition _delta : ident := $"delta".
Definition _digit : ident := $"digit".
Definition _encode : ident := $"encode".
Definition _encoding : ident := $"encoding".
Definition _firsttime : ident := $"firsttime".
Definition _gp_assert : ident := $"gp_assert".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _j__2 : ident := $"j__2".
Definition _k : ident := $"k".
Definition _largest : ident := $"largest".
Definition _len : ident := $"len".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _min : ident := $"min".
Definition _n : ident := $"n".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _numpoints : ident := $"numpoints".
Definition _ossl_punycode_decode : ident := $"ossl_punycode_decode".
Definition _out : ident := $"out".
Definition _put : ident := $"put".
Definition _q : ident := $"q".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _rfc_adapt : ident := $"rfc_adapt".
Definition _room : ident := $"room".
Definition _t : ident := $"t".
Definition _uints_eq : ident := $"uints_eq".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _values : ident := $"values".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition f_any_uints := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_values, (tptr tuint)) :: (_i, tulong) :: (_t'3, tuint) ::
               (_t'2, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default))
      ((Ebinop Omul (Etempvar _n tulong) (Esizeof tuint tulong) tulong) ::
       nil))
    (Sset _values (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _values (tptr tuint))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sset _t'2
                (Ecast
                  (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong) tint)
                  tbool))
              (Sset _t'2 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _values (tptr tuint))
                  (Etempvar _i tulong) (tptr tuint)) tuint)
              (Etempvar _t'3 tuint))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Etempvar _values (tptr tuint))))))
|}.

Definition f_uints_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_b, (tptr tuint)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
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
              (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tulong)
                (tptr tuint)) tuint))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tulong)
                  (tptr tuint)) tuint))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuint)
                           (Etempvar _t'2 tuint) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_rfc_adapt := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_delta, tulong) :: (_numpoints, tulong) ::
                (_firsttime, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _k (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sifthenelse (Etempvar _firsttime tint)
        (Sset _t'1
          (Ecast
            (Ebinop Odiv (Etempvar _delta tulong)
              (Econst_int (Int.repr 700) tint) tulong) tulong))
        (Sset _t'1
          (Ecast
            (Ebinop Odiv (Etempvar _delta tulong)
              (Econst_int (Int.repr 2) tint) tulong) tulong)))
      (Sset _delta (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _delta
        (Ebinop Oadd (Etempvar _delta tulong)
          (Ebinop Odiv (Etempvar _delta tulong) (Etempvar _numpoints tulong)
            tulong) tulong))
      (Ssequence
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _delta tulong)
                           (Econst_int (Int.repr 455) tint) tint)
              Sskip
              Sbreak)
            (Sset _delta
              (Ebinop Odiv (Etempvar _delta tulong)
                (Econst_int (Int.repr 35) tint) tulong)))
          (Sset _k
            (Ebinop Oadd (Etempvar _k tulong) (Econst_int (Int.repr 36) tint)
              tulong)))
        (Sreturn (Some (Ebinop Oadd (Etempvar _k tulong)
                         (Ebinop Odiv
                           (Ebinop Omul (Econst_int (Int.repr 36) tint)
                             (Etempvar _delta tulong) tulong)
                           (Ebinop Oadd (Etempvar _delta tulong)
                             (Econst_int (Int.repr 38) tint) tulong) tulong)
                         tulong)))))))
|}.

Definition f_put := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_room, tulong) ::
                (_len, (tptr tulong)) :: (_c, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3 (Ederef (Etempvar _len (tptr tulong)) tulong))
    (Sifthenelse (Ebinop Oge (Etempvar _t'3 tulong) (Etempvar _room tulong)
                   tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _len (tptr tulong)) tulong))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _out (tptr tuchar)) (Etempvar _t'2 tulong)
            (tptr tuchar)) tuchar) (Ecast (Etempvar _c tulong) tuchar)))
    (Ssequence
      (Ssequence
        (Sset _t'1 (Ederef (Etempvar _len (tptr tulong)) tulong))
        (Sassign (Ederef (Etempvar _len (tptr tulong)) tulong)
          (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
            tulong)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_digit := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_d, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _d tulong)
                 (Econst_int (Int.repr 26) tint) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Oadd (Econst_int (Int.repr 97) tint) (Etempvar _d tulong)
          tulong) tulong))
    (Sset _t'1
      (Ecast
        (Ebinop Osub
          (Ebinop Oadd (Econst_int (Int.repr 48) tint) (Etempvar _d tulong)
            tulong) (Econst_int (Int.repr 26) tint) tulong) tulong)))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_encode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_cps, (tptr tuint)) :: (_m, tulong) ::
                (_out, (tptr tuchar)) :: (_room, tulong) ::
                (_len, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_delta, tulong) :: (_bias, tulong) ::
               (_b, tulong) :: (_h, tulong) :: (_q, tulong) ::
               (_k, tulong) :: (_t, tulong) :: (_j, tulong) ::
               (_min, tulong) :: (_j__1, tulong) :: (_j__2, tulong) ::
               (_t'11, tulong) :: (_t'10, tint) :: (_t'9, tulong) ::
               (_t'8, tint) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, tuint) ::
               (_t'14, tuint) :: (_t'13, tuint) :: (_t'12, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Ecast (Econst_int (Int.repr 128) tint) tulong))
  (Ssequence
    (Sset _delta (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _bias (Ecast (Econst_int (Int.repr 72) tint) tulong))
      (Ssequence
        (Sset _b (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sassign (Ederef (Etempvar _len (tptr tulong)) tulong)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                 (Etempvar _m tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'17
                      (Ederef
                        (Ebinop Oadd (Etempvar _cps (tptr tuint))
                          (Etempvar _j tulong) (tptr tuint)) tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'17 tuint)
                                   (Econst_int (Int.repr 128) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'18
                              (Ederef
                                (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                  (Etempvar _j tulong) (tptr tuint)) tuint))
                            (Scall (Some _t'1)
                              (Evar _put (Tfunction
                                           ((tptr tuchar) :: tulong ::
                                            (tptr tulong) :: tulong :: nil)
                                           tint cc_default))
                              ((Etempvar _out (tptr tuchar)) ::
                               (Etempvar _room tulong) ::
                               (Etempvar _len (tptr tulong)) ::
                               (Etempvar _t'18 tuint) :: nil)))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint)
                                         tint)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            Sskip))
                        (Sset _b
                          (Ebinop Oadd (Etempvar _b tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))
                      Sskip)))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _b tulong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _put (Tfunction
                                   ((tptr tuchar) :: tulong ::
                                    (tptr tulong) :: tulong :: nil) tint
                                   cc_default))
                      ((Etempvar _out (tptr tuchar)) ::
                       (Etempvar _room tulong) ::
                       (Etempvar _len (tptr tulong)) ::
                       (Econst_int (Int.repr 45) tint) :: nil))
                    (Sset _t'2
                      (Ecast (Eunop Onotbool (Etempvar _t'3 tint) tint)
                        tbool)))
                  (Sset _t'2 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'2 tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Sset _h (Etempvar _b tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _h tulong)
                                     (Etempvar _m tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _min (Econst_long (Int64.repr (-1)) tulong))
                        (Ssequence
                          (Ssequence
                            (Sset _j__1
                              (Ecast (Econst_int (Int.repr 0) tint) tulong))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _j__1 tulong)
                                               (Etempvar _m tulong) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'15
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _cps (tptr tuint))
                                          (Etempvar _j__1 tulong)
                                          (tptr tuint)) tuint))
                                    (Sifthenelse (Ebinop Oge
                                                   (Etempvar _t'15 tuint)
                                                   (Etempvar _n tulong) tint)
                                      (Ssequence
                                        (Sset _t'16
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _cps (tptr tuint))
                                              (Etempvar _j__1 tulong)
                                              (tptr tuint)) tuint))
                                        (Sset _t'4
                                          (Ecast
                                            (Ebinop Olt
                                              (Etempvar _t'16 tuint)
                                              (Etempvar _min tulong) tint)
                                            tbool)))
                                      (Sset _t'4
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'4 tint)
                                    (Ssequence
                                      (Sset _t'14
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _cps (tptr tuint))
                                            (Etempvar _j__1 tulong)
                                            (tptr tuint)) tuint))
                                      (Sset _min
                                        (Ecast (Etempvar _t'14 tuint) tulong)))
                                    Sskip)))
                              (Sset _j__1
                                (Ebinop Oadd (Etempvar _j__1 tulong)
                                  (Econst_int (Int.repr 1) tint) tulong))))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Ogt
                                             (Etempvar _delta tulong)
                                             (Econst_int (Int.repr (-1)) tuint)
                                             tint)
                                (Sset _t'5 (Econst_int (Int.repr 1) tint))
                                (Sset _t'5
                                  (Ecast
                                    (Ebinop Ogt
                                      (Ebinop Osub (Etempvar _min tulong)
                                        (Etempvar _n tulong) tulong)
                                      (Ebinop Odiv
                                        (Ebinop Osub
                                          (Econst_int (Int.repr (-1)) tuint)
                                          (Etempvar _delta tulong) tulong)
                                        (Ebinop Oadd (Etempvar _h tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong) tulong) tint) tbool)))
                              (Sifthenelse (Etempvar _t'5 tint)
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                Sskip))
                            (Ssequence
                              (Sset _delta
                                (Ebinop Oadd (Etempvar _delta tulong)
                                  (Ebinop Omul
                                    (Ebinop Osub (Etempvar _min tulong)
                                      (Etempvar _n tulong) tulong)
                                    (Ebinop Oadd (Etempvar _h tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)
                                    tulong) tulong))
                              (Ssequence
                                (Sset _n (Etempvar _min tulong))
                                (Ssequence
                                  (Ssequence
                                    (Sset _j__2
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tulong))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _j__2 tulong)
                                                       (Etempvar _m tulong)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'13
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _cps (tptr tuint))
                                                  (Etempvar _j__2 tulong)
                                                  (tptr tuint)) tuint))
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _t'13 tuint)
                                                           (Etempvar _n tulong)
                                                           tint)
                                              (Ssequence
                                                (Sset _delta
                                                  (Ebinop Oadd
                                                    (Etempvar _delta tulong)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tulong))
                                                (Sifthenelse (Ebinop Ogt
                                                               (Etempvar _delta tulong)
                                                               (Econst_int (Int.repr (-1)) tuint)
                                                               tint)
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                  Sskip))
                                              Sskip))
                                          (Ssequence
                                            (Sset _t'12
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _cps (tptr tuint))
                                                  (Etempvar _j__2 tulong)
                                                  (tptr tuint)) tuint))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _t'12 tuint)
                                                           (Etempvar _n tulong)
                                                           tint)
                                              (Ssequence
                                                (Sset _q
                                                  (Etempvar _delta tulong))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _k
                                                      (Ecast
                                                        (Econst_int (Int.repr 36) tint)
                                                        tulong))
                                                    (Sloop
                                                      (Ssequence
                                                        Sskip
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Ole
                                                                (Etempvar _k tulong)
                                                                (Etempvar _bias tulong)
                                                                tint)
                                                              (Sset _t'6
                                                                (Ecast
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tulong))
                                                              (Sifthenelse 
                                                                (Ebinop Oge
                                                                  (Etempvar _k tulong)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _bias tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'6
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                  (Sset _t'6
                                                                    (Ecast
                                                                    (Etempvar _t'6 tulong)
                                                                    tulong)))
                                                                (Ssequence
                                                                  (Sset _t'6
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _k tulong)
                                                                    (Etempvar _bias tulong)
                                                                    tulong)
                                                                    tulong))
                                                                  (Sset _t'6
                                                                    (Ecast
                                                                    (Etempvar _t'6 tulong)
                                                                    tulong)))))
                                                            (Sset _t
                                                              (Etempvar _t'6 tulong)))
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _q tulong)
                                                                (Etempvar _t tulong)
                                                                tint)
                                                              Sbreak
                                                              Sskip)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'7)
                                                                    (Evar _digit 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _t tulong)
                                                                    (Ebinop Omod
                                                                    (Ebinop Osub
                                                                    (Etempvar _q tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                  (Scall (Some _t'8)
                                                                    (Evar _put 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tulong) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _out (tptr tuchar)) ::
                                                                    (Etempvar _room tulong) ::
                                                                    (Etempvar _len (tptr tulong)) ::
                                                                    (Etempvar _t'7 tulong) ::
                                                                    nil)))
                                                                (Sifthenelse 
                                                                  (Eunop Onotbool
                                                                    (Etempvar _t'8 tint)
                                                                    tint)
                                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                  Sskip))
                                                              (Sset _q
                                                                (Ebinop Odiv
                                                                  (Ebinop Osub
                                                                    (Etempvar _q tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                  (Ebinop Osub
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                  tulong))))))
                                                      (Sset _k
                                                        (Ebinop Oadd
                                                          (Etempvar _k tulong)
                                                          (Econst_int (Int.repr 36) tint)
                                                          tulong))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'9)
                                                          (Evar _digit 
                                                          (Tfunction
                                                            (tulong :: nil)
                                                            tulong
                                                            cc_default))
                                                          ((Etempvar _q tulong) ::
                                                           nil))
                                                        (Scall (Some _t'10)
                                                          (Evar _put 
                                                          (Tfunction
                                                            ((tptr tuchar) ::
                                                             tulong ::
                                                             (tptr tulong) ::
                                                             tulong :: nil)
                                                            tint cc_default))
                                                          ((Etempvar _out (tptr tuchar)) ::
                                                           (Etempvar _room tulong) ::
                                                           (Etempvar _len (tptr tulong)) ::
                                                           (Etempvar _t'9 tulong) ::
                                                           nil)))
                                                      (Sifthenelse (Eunop Onotbool
                                                                    (Etempvar _t'10 tint)
                                                                    tint)
                                                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                        Sskip))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'11)
                                                          (Evar _rfc_adapt 
                                                          (Tfunction
                                                            (tulong ::
                                                             tulong ::
                                                             tint :: nil)
                                                            tulong
                                                            cc_default))
                                                          ((Etempvar _delta tulong) ::
                                                           (Ebinop Oadd
                                                             (Etempvar _h tulong)
                                                             (Econst_int (Int.repr 1) tint)
                                                             tulong) ::
                                                           (Ebinop Oeq
                                                             (Etempvar _h tulong)
                                                             (Etempvar _b tulong)
                                                             tint) :: nil))
                                                        (Sset _bias
                                                          (Etempvar _t'11 tulong)))
                                                      (Ssequence
                                                        (Sset _delta
                                                          (Ecast
                                                            (Econst_int (Int.repr 0) tint)
                                                            tulong))
                                                        (Sset _h
                                                          (Ebinop Oadd
                                                            (Etempvar _h tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))))))
                                              Sskip))))
                                      (Sset _j__2
                                        (Ebinop Oadd (Etempvar _j__2 tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong))))
                                  (Sset _delta
                                    (Ebinop Oadd (Etempvar _delta tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))))))))
                    (Sset _n
                      (Ebinop Oadd (Etempvar _n tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_len, tulong) :: (_count, tuint) :: nil);
  fn_temps := ((_m, tulong) :: (_room, tulong) :: (_cps, (tptr tuint)) ::
               (_out, (tptr tuint)) :: (_encoding, (tptr tuchar)) ::
               (_largest, tulong) :: (_j, tulong) :: (_r, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tulong) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr tuint)) :: (_t'3, (tptr tuint)) ::
               (_t'2, tulong) :: (_t'1, tulong) :: (_t'21, tulong) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tulong) ::
               (_t'17, tuint) :: (_t'16, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
        ((Ebinop Odiv (Econst_long (Int64.repr 9223372036854775807) tlong)
           (Esizeof tuint tulong) tulong) :: nil))
      (Sset _m (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
          ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
        (Sset _room (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _any_uints (Tfunction (tulong :: nil) (tptr tuint)
                               cc_default)) ((Etempvar _m tulong) :: nil))
          (Sset _cps (Etempvar _t'3 (tptr tuint))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _any_uints (Tfunction (tulong :: nil) (tptr tuint)
                                 cc_default)) ((Etempvar _m tulong) :: nil))
            (Sset _out (Etempvar _t'4 (tptr tuint))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                           (tptr tvoid) cc_default))
                ((Etempvar _room tulong) :: nil))
              (Sset _encoding (Etempvar _t'5 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _cps (tptr tuint))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Sset _t'6 (Econst_int (Int.repr 1) tint))
                        (Sset _t'6
                          (Ecast
                            (Ebinop Oeq (Etempvar _out (tptr tuint))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint) tbool)))
                      (Sifthenelse (Etempvar _t'6 tint)
                        (Sset _t'7 (Econst_int (Int.repr 1) tint))
                        (Sset _t'7
                          (Ecast
                            (Ebinop Oeq (Etempvar _encoding (tptr tuchar))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint) tbool))))
                    (Sifthenelse (Etempvar _t'7 tint)
                      (Sset _t'8 (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _encode (Tfunction
                                          ((tptr tuint) :: tulong ::
                                           (tptr tuchar) :: tulong ::
                                           (tptr tulong) :: nil) tint
                                          cc_default))
                          ((Etempvar _cps (tptr tuint)) ::
                           (Etempvar _m tulong) ::
                           (Etempvar _encoding (tptr tuchar)) ::
                           (Etempvar _room tulong) ::
                           (Eaddrof (Evar _len tulong) (tptr tulong)) :: nil))
                        (Sset _t'8
                          (Ecast (Eunop Onotbool (Etempvar _t'9 tint) tint)
                            tbool)))))
                  (Sifthenelse (Etempvar _t'8 tint)
                    (Sset _t'10 (Econst_int (Int.repr 1) tint))
                    (Ssequence
                      (Sset _t'21 (Evar _len tulong))
                      (Sset _t'10
                        (Ecast
                          (Ebinop Oge (Etempvar _t'21 tulong)
                            (Econst_int (Int.repr (-1)) tuint) tint) tbool)))))
                (Sifthenelse (Etempvar _t'10 tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Sset _largest (Ecast (Econst_int (Int.repr 0) tint) tulong))
                (Ssequence
                  (Ssequence
                    (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                       (Etempvar _m tulong) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _t'19
                              (Ederef
                                (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                  (Etempvar _j tulong) (tptr tuint)) tuint))
                            (Sifthenelse (Ebinop Ogt (Etempvar _t'19 tuint)
                                           (Etempvar _largest tulong) tint)
                              (Ssequence
                                (Sset _t'20
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                      (Etempvar _j tulong) (tptr tuint))
                                    tuint))
                                (Sset _t'11
                                  (Ecast (Etempvar _t'20 tuint) tulong)))
                              (Sset _t'11
                                (Ecast (Etempvar _largest tulong) tulong))))
                          (Sset _largest (Etempvar _t'11 tulong))))
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tulong)
                          (Econst_int (Int.repr 1) tint) tulong))))
                  (Ssequence
                    (Sassign (Evar _count tuint)
                      (Ecast (Etempvar _m tulong) tuint))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'18 (Evar _len tulong))
                          (Scall (Some _t'12)
                            (Evar _ossl_punycode_decode (Tfunction
                                                          ((tptr tschar) ::
                                                           tulong ::
                                                           (tptr tuint) ::
                                                           (tptr tuint) ::
                                                           nil) tint
                                                          cc_default))
                            ((Ecast (Etempvar _encoding (tptr tuchar))
                               (tptr tschar)) :: (Etempvar _t'18 tulong) ::
                             (Etempvar _out (tptr tuint)) ::
                             (Eaddrof (Evar _count tuint) (tptr tuint)) ::
                             nil)))
                        (Sset _r (Etempvar _t'12 tint)))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Ole (Etempvar _largest tulong)
                                         (Econst_int (Int.repr 127) tint)
                                         tint)
                            (Sset _t'13 (Econst_int (Int.repr 1) tint))
                            (Sset _t'13
                              (Ecast
                                (Ebinop Ole
                                  (Ebinop Osub (Etempvar _largest tulong)
                                    (Econst_int (Int.repr 127) tint) tulong)
                                  (Ebinop Odiv
                                    (Ebinop Oshl
                                      (Ecast (Econst_int (Int.repr 1) tint)
                                        tulong)
                                      (Econst_int (Int.repr 32) tint) tulong)
                                    (Etempvar _m tulong) tulong) tint) tbool)))
                          (Sifthenelse (Etempvar _t'13 tint)
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Ebinop Oeq (Etempvar _r tint)
                                 (Econst_int (Int.repr 1) tint) tint) :: nil))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Ssequence
                                (Sset _t'17 (Evar _count tuint))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'17 tuint)
                                               (Etempvar _m tulong) tint)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'15)
                                        (Evar _uints_eq (Tfunction
                                                          ((tptr tuint) ::
                                                           (tptr tuint) ::
                                                           tulong :: nil)
                                                          tint cc_default))
                                        ((Etempvar _out (tptr tuint)) ::
                                         (Etempvar _cps (tptr tuint)) ::
                                         (Etempvar _m tulong) :: nil))
                                      (Sset _t'14
                                        (Ecast (Etempvar _t'15 tint) tbool)))
                                    (Sset _t'14
                                      (Ecast (Etempvar _t'14 tint) tint)))
                                  (Sset _t'14
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tint))))
                              (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'16 (Evar _count tuint))
                                    (Sset _t'14
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'16 tuint)
                                          (Etempvar _m tulong) tint) tbool)))
                                  (Sset _t'14
                                    (Ecast (Etempvar _t'14 tint) tint)))
                                (Sset _t'14
                                  (Ecast (Econst_int (Int.repr 0) tint) tint))))
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Etempvar _t'14 tint) :: nil)))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))
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
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_ossl_punycode_decode,
   Gfun(External (EF_external "ossl_punycode_decode"
                   (mksignature
                     (AST.Xptr :: AST.Xlong :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr tschar) :: tulong :: (tptr tuint) :: (tptr tuint) :: nil) tint
     cc_default)) :: (_upto, Gfun(Internal f_upto)) ::
 (_any_uints, Gfun(Internal f_any_uints)) ::
 (_uints_eq, Gfun(Internal f_uints_eq)) ::
 (_rfc_adapt, Gfun(Internal f_rfc_adapt)) :: (_put, Gfun(Internal f_put)) ::
 (_digit, Gfun(Internal f_digit)) :: (_encode, Gfun(Internal f_encode)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ossl_punycode_decode :: _gp_assert :: _nondet_size ::
 _nondet_u32 :: _quickproof_malloc :: ___builtin_debug ::
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


