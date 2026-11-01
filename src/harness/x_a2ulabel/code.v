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
  Definition source_file := "harness/x_a2ulabel.c".
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
Definition _b : ident := $"b".
Definition _bias : ident := $"bias".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _cap : ident := $"cap".
Definition _copy_bytes : ident := $"copy_bytes".
Definition _count : ident := $"count".
Definition _cps : ident := $"cps".
Definition _d : ident := $"d".
Definition _delta : ident := $"delta".
Definition _digit : ident := $"digit".
Definition _e : ident := $"e".
Definition _firsttime : ident := $"firsttime".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _mode : ident := $"mode".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _nul : ident := $"nul".
Definition _numpoints : ident := $"numpoints".
Definition _o : ident := $"o".
Definition _ok : ident := $"ok".
Definition _oldi : ident := $"oldi".
Definition _ossl_a2ulabel : ident := $"ossl_a2ulabel".
Definition _ossl_shim_fail_next : ident := $"ossl_shim_fail_next".
Definition _ossl_shim_live : ident := $"ossl_shim_live".
Definition _ossl_shim_zalloc_failed : ident := $"ossl_shim_zalloc_failed".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _p : ident := $"p".
Definition _pos : ident := $"pos".
Definition _pr_a2ulabel : ident := $"pr_a2ulabel".
Definition _pr_adapt : ident := $"pr_adapt".
Definition _pr_dec : ident := $"pr_dec".
Definition _pr_decode : ident := $"pr_decode".
Definition _pr_digit_value : ident := $"pr_digit_value".
Definition _pr_put : ident := $"pr_put".
Definition _pr_sink : ident := $"pr_sink".
Definition _pr_threshold : ident := $"pr_threshold".
Definition _pr_utf8 : ident := $"pr_utf8".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _s : ident := $"s".
Definition _same_bytes : ident := $"same_bytes".
Definition _sep : ident := $"sep".
Definition _short_ : ident := $"short_".
Definition _sl : ident := $"sl".
Definition _snap : ident := $"snap".
Definition _st : ident := $"st".
Definition _t : ident := $"t".
Definition _u : ident := $"u".
Definition _ul : ident := $"ul".
Definition _w : ident := $"w".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_pr_digit_value := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_c, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _c tuchar)
                   (Econst_int (Int.repr 65) tint) tint)
      (Sset _t'1
        (Ecast
          (Ebinop Ole (Etempvar _c tuchar) (Econst_int (Int.repr 90) tint)
            tint) tbool))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ebinop Osub (Ecast (Etempvar _c tuchar) tulong)
                       (Econst_int (Int.repr 65) tint) tulong)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _c tuchar)
                     (Econst_int (Int.repr 97) tint) tint)
        (Sset _t'2
          (Ecast
            (Ebinop Ole (Etempvar _c tuchar) (Econst_int (Int.repr 122) tint)
              tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sreturn (Some (Ebinop Osub (Ecast (Etempvar _c tuchar) tulong)
                         (Econst_int (Int.repr 97) tint) tulong)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _c tuchar)
                       (Econst_int (Int.repr 48) tint) tint)
          (Sset _t'3
            (Ecast
              (Ebinop Ole (Etempvar _c tuchar)
                (Econst_int (Int.repr 57) tint) tint) tbool))
          (Sset _t'3 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'3 tint)
          (Sreturn (Some (Ebinop Oadd
                           (Ebinop Osub (Ecast (Etempvar _c tuchar) tulong)
                             (Econst_int (Int.repr 48) tint) tulong)
                           (Econst_int (Int.repr 26) tint) tulong)))
          Sskip))
      (Sreturn (Some (Econst_long (Int64.repr 36) tulong))))))
|}.

Definition f_pr_threshold := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_k, tulong) :: (_bias, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _k tulong) (Etempvar _bias tulong) tint)
    (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _k tulong)
                   (Ebinop Oadd (Etempvar _bias tulong)
                     (Econst_long (Int64.repr 26) tulong) tulong) tint)
      (Sreturn (Some (Econst_long (Int64.repr 26) tulong)))
      Sskip)
    (Sreturn (Some (Ebinop Osub (Etempvar _k tulong) (Etempvar _bias tulong)
                     tulong)))))
|}.

Definition f_pr_adapt := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_delta, tulong) :: (_numpoints, tulong) ::
                (_firsttime, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _k (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sifthenelse (Etempvar _firsttime tint)
      (Sset _delta
        (Ebinop Odiv (Etempvar _delta tulong)
          (Econst_long (Int64.repr 700) tulong) tulong))
      (Sset _delta
        (Ebinop Odiv (Etempvar _delta tulong) (Econst_int (Int.repr 2) tint)
          tulong)))
    (Ssequence
      (Sset _delta
        (Ebinop Oadd (Etempvar _delta tulong)
          (Ebinop Odiv (Etempvar _delta tulong) (Etempvar _numpoints tulong)
            tulong) tulong))
      (Ssequence
        (Swhile
          (Ebinop Ogt (Etempvar _delta tulong)
            (Ebinop Odiv
              (Ebinop Omul
                (Ebinop Osub (Econst_long (Int64.repr 36) tulong)
                  (Econst_long (Int64.repr 1) tulong) tulong)
                (Econst_long (Int64.repr 26) tulong) tulong)
              (Econst_int (Int.repr 2) tint) tulong) tint)
          (Ssequence
            (Sset _delta
              (Ebinop Odiv (Etempvar _delta tulong)
                (Ebinop Osub (Econst_long (Int64.repr 36) tulong)
                  (Econst_long (Int64.repr 1) tulong) tulong) tulong))
            (Sset _k
              (Ebinop Oadd (Etempvar _k tulong)
                (Econst_long (Int64.repr 36) tulong) tulong))))
        (Sreturn (Some (Ebinop Oadd (Etempvar _k tulong)
                         (Ebinop Odiv
                           (Ebinop Omul
                             (Ebinop Oadd
                               (Ebinop Osub
                                 (Econst_long (Int64.repr 36) tulong)
                                 (Econst_long (Int64.repr 1) tulong) tulong)
                               (Econst_int (Int.repr 1) tint) tulong)
                             (Etempvar _delta tulong) tulong)
                           (Ebinop Oadd (Etempvar _delta tulong)
                             (Econst_long (Int64.repr 38) tulong) tulong)
                           tulong) tulong)))))))
|}.

Definition f_pr_decode := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tuchar)) :: (_len, tulong) ::
                (_out, (tptr tuint)) :: (_cap, tulong) ::
                (_d, (tptr (Tstruct _pr_dec noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tulong) :: (_j, tulong) :: (_pos, tulong) ::
               (_n, tulong) :: (_i, tulong) :: (_bias, tulong) ::
               (_oldi, tulong) :: (_w, tulong) :: (_k, tulong) ::
               (_digit, tulong) :: (_t, tulong) :: (_outlen, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) ::
               (_t'8, tuchar) :: (_t'7, tuchar) :: (_t'6, tuchar) ::
               (_t'5, tuchar) :: (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
          (Tstruct _pr_dec noattr)) _ok tint) (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
            (Tstruct _pr_dec noattr)) _count tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                             (Etempvar _len tulong) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'8
                  (Ederef
                    (Ebinop Oadd (Etempvar _in (tptr tuchar))
                      (Etempvar _j tulong) (tptr tuchar)) tuchar))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuchar)
                               (Econst_int (Int.repr 45) tint) tint)
                  (Sset _b (Etempvar _j tulong))
                  Sskip)))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tulong)
                (Econst_int (Int.repr 1) tint) tulong))))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _b tulong)
                         (Etempvar _cap tulong) tint)
            (Sreturn None)
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                 (Etempvar _b tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Ebinop Oadd (Etempvar _in (tptr tuchar))
                            (Etempvar _j tulong) (tptr tuchar)) tuchar))
                      (Sifthenelse (Ebinop Oge (Etempvar _t'7 tuchar)
                                     (Econst_int (Int.repr 128) tint) tint)
                        (Sreturn None)
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Ederef
                            (Ebinop Oadd (Etempvar _in (tptr tuchar))
                              (Etempvar _j tulong) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _out (tptr tuint))
                              (Etempvar _j tulong) (tptr tuint)) tuint)
                          (Etempvar _t'6 tuchar)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
                            (Tstruct _pr_dec noattr)) _count tulong)
                        (Ebinop Oadd (Etempvar _j tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))
            (Ssequence
              (Sset _pos (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _b tulong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sset _pos
                    (Ebinop Oadd (Etempvar _b tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  Sskip)
                (Ssequence
                  (Sset _n (Econst_long (Int64.repr 128) tulong))
                  (Ssequence
                    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                    (Ssequence
                      (Sset _bias (Econst_long (Int64.repr 72) tulong))
                      (Ssequence
                        (Swhile
                          (Ebinop Olt (Etempvar _pos tulong)
                            (Etempvar _len tulong) tint)
                          (Ssequence
                            (Sset _oldi (Etempvar _i tulong))
                            (Ssequence
                              (Sset _w
                                (Ecast (Econst_int (Int.repr 1) tint) tulong))
                              (Ssequence
                                (Sset _k
                                  (Econst_long (Int64.repr 36) tulong))
                                (Ssequence
                                  (Sloop
                                    (Ssequence
                                      Sskip
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oge
                                                       (Etempvar _pos tulong)
                                                       (Etempvar _len tulong)
                                                       tint)
                                          (Sreturn None)
                                          Sskip)
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _in (tptr tuchar))
                                                    (Etempvar _pos tulong)
                                                    (tptr tuchar)) tuchar))
                                              (Scall (Some _t'1)
                                                (Evar _pr_digit_value 
                                                (Tfunction (tuchar :: nil)
                                                  tulong cc_default))
                                                ((Etempvar _t'5 tuchar) ::
                                                 nil)))
                                            (Sset _digit
                                              (Etempvar _t'1 tulong)))
                                          (Ssequence
                                            (Sset _pos
                                              (Ebinop Oadd
                                                (Etempvar _pos tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oge
                                                             (Etempvar _digit tulong)
                                                             (Econst_long (Int64.repr 36) tulong)
                                                             tint)
                                                (Sreturn None)
                                                Sskip)
                                              (Ssequence
                                                (Sset _i
                                                  (Ebinop Oadd
                                                    (Etempvar _i tulong)
                                                    (Ebinop Omul
                                                      (Etempvar _digit tulong)
                                                      (Etempvar _w tulong)
                                                      tulong) tulong))
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Etempvar _i tulong)
                                                                 (Econst_long (Int64.repr 4294967295) tulong)
                                                                 tint)
                                                    (Sreturn None)
                                                    Sskip)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'2)
                                                        (Evar _pr_threshold 
                                                        (Tfunction
                                                          (tulong ::
                                                           tulong :: nil)
                                                          tulong cc_default))
                                                        ((Etempvar _k tulong) ::
                                                         (Etempvar _bias tulong) ::
                                                         nil))
                                                      (Sset _t
                                                        (Etempvar _t'2 tulong)))
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _digit tulong)
                                                                    (Etempvar _t tulong)
                                                                    tint)
                                                        Sbreak
                                                        Sskip)
                                                      (Ssequence
                                                        (Sset _w
                                                          (Ebinop Omul
                                                            (Etempvar _w tulong)
                                                            (Ebinop Osub
                                                              (Econst_long (Int64.repr 36) tulong)
                                                              (Etempvar _t tulong)
                                                              tulong) tulong))
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Ogt
                                                              (Etempvar _w tulong)
                                                              (Econst_long (Int64.repr 4294967295) tulong)
                                                              tint)
                                                            (Sreturn None)
                                                            Sskip)
                                                          (Sset _k
                                                            (Ebinop Oadd
                                                              (Etempvar _k tulong)
                                                              (Econst_long (Int64.repr 36) tulong)
                                                              tulong)))))))))))))
                                    Sskip)
                                  (Ssequence
                                    (Sset _outlen
                                      (Efield
                                        (Ederef
                                          (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
                                          (Tstruct _pr_dec noattr)) _count
                                        tulong))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'3)
                                          (Evar _pr_adapt (Tfunction
                                                            (tulong ::
                                                             tulong ::
                                                             tint :: nil)
                                                            tulong
                                                            cc_default))
                                          ((Ebinop Osub (Etempvar _i tulong)
                                             (Etempvar _oldi tulong) tulong) ::
                                           (Ebinop Oadd
                                             (Ecast (Etempvar _outlen tulong)
                                               tulong)
                                             (Econst_int (Int.repr 1) tint)
                                             tulong) ::
                                           (Ebinop Oeq
                                             (Etempvar _oldi tulong)
                                             (Econst_int (Int.repr 0) tint)
                                             tint) :: nil))
                                        (Sset _bias (Etempvar _t'3 tulong)))
                                      (Ssequence
                                        (Sset _n
                                          (Ebinop Oadd (Etempvar _n tulong)
                                            (Ebinop Odiv (Etempvar _i tulong)
                                              (Ebinop Oadd
                                                (Ecast
                                                  (Etempvar _outlen tulong)
                                                  tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong) tulong) tulong))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _n tulong)
                                                         (Econst_long (Int64.repr 4294967295) tulong)
                                                         tint)
                                            (Sreturn None)
                                            Sskip)
                                          (Ssequence
                                            (Sset _i
                                              (Ebinop Omod
                                                (Etempvar _i tulong)
                                                (Ebinop Oadd
                                                  (Ecast
                                                    (Etempvar _outlen tulong)
                                                    tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong) tulong))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oge
                                                             (Etempvar _outlen tulong)
                                                             (Etempvar _cap tulong)
                                                             tint)
                                                (Sreturn None)
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _j
                                                    (Etempvar _outlen tulong))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Ogt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _i tulong)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _t'4
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _out (tptr tuint))
                                                              (Ebinop Osub
                                                                (Etempvar _j tulong)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tulong)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _out (tptr tuint))
                                                              (Etempvar _j tulong)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'4 tuint))))
                                                    (Sset _j
                                                      (Ebinop Osub
                                                        (Etempvar _j tulong)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tulong))))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _out (tptr tuint))
                                                        (Etempvar _i tulong)
                                                        (tptr tuint)) tuint)
                                                    (Ecast
                                                      (Etempvar _n tulong)
                                                      tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
                                                          (Tstruct _pr_dec noattr))
                                                        _count tulong)
                                                      (Ebinop Oadd
                                                        (Etempvar _outlen tulong)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tulong))
                                                    (Sset _i
                                                      (Ebinop Oadd
                                                        (Etempvar _i tulong)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tulong))))))))))))))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _d (tptr (Tstruct _pr_dec noattr)))
                              (Tstruct _pr_dec noattr)) _ok tint)
                          (Econst_int (Int.repr 1) tint))))))))))))))
|}.

Definition f_pr_utf8 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_c, tulong) :: (_o, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _c tulong)
                 (Econst_int (Int.repr 128) tint) tint)
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _o (tptr tuchar))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Ecast (Etempvar _c tulong) tuchar))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _c tulong)
                   (Econst_int (Int.repr 2048) tint) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _o (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oadd (Econst_int (Int.repr 192) tint)
              (Ebinop Odiv (Etempvar _c tulong)
                (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                (Ebinop Omod (Etempvar _c tulong)
                  (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
          (Sreturn (Some (Econst_int (Int.repr 2) tint)))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _c tulong)
                     (Econst_int (Int.repr 65536) tint) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oadd (Econst_int (Int.repr 224) tint)
                (Ebinop Odiv (Etempvar _c tulong)
                  (Econst_int (Int.repr 4096) tint) tulong) tulong) tuchar))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                  (Ebinop Omod
                    (Ebinop Odiv (Etempvar _c tulong)
                      (Econst_int (Int.repr 64) tint) tulong)
                    (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                    (Ebinop Omod (Etempvar _c tulong)
                      (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
              (Sreturn (Some (Econst_int (Int.repr 3) tint))))))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _c tulong)
                       (Econst_int (Int.repr 1114111) tint) tint)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oadd (Econst_int (Int.repr 240) tint)
                  (Ebinop Odiv (Etempvar _c tulong)
                    (Econst_int (Int.repr 262144) tint) tulong) tulong)
                tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                    (Ebinop Omod
                      (Ebinop Odiv (Etempvar _c tulong)
                        (Econst_int (Int.repr 4096) tint) tulong)
                      (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tuchar))
                      (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                  (Ecast
                    (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                      (Ebinop Omod
                        (Ebinop Odiv (Etempvar _c tulong)
                          (Econst_int (Int.repr 64) tint) tulong)
                        (Econst_int (Int.repr 64) tint) tulong) tulong)
                    tuchar))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _o (tptr tuchar))
                        (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                    (Ecast
                      (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                        (Ebinop Omod (Etempvar _c tulong)
                          (Econst_int (Int.repr 64) tint) tulong) tulong)
                      tuchar))
                  (Sreturn (Some (Econst_int (Int.repr 4) tint)))))))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_pr_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, (tptr (Tstruct _pr_sink noattr))) ::
                (_p, (tptr tuchar)) :: (_m, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tuchar) :: (_t'3, tulong) :: (_t'2, (tptr tuchar)) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _m tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
            (Tstruct _pr_sink noattr)) _cap tulong))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
              (Tstruct _pr_sink noattr)) _len tulong))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'5 tulong)
                         (Etempvar _t'6 tulong) tulong) (Etempvar _m tulong)
                       tint)
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
                  (Tstruct _pr_sink noattr)) _short_ tint)
              (Econst_int (Int.repr 1) tint))
            (Sreturn None))
          Sskip)))
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
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
                    (Tstruct _pr_sink noattr)) _buf (tptr tuchar)))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
                      (Tstruct _pr_sink noattr)) _len tulong))
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Etempvar _p (tptr tuchar))
                        (Etempvar _j tulong) (tptr tuchar)) tuchar))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'2 (tptr tuchar))
                        (Ebinop Oadd (Etempvar _t'3 tulong)
                          (Etempvar _j tulong) tulong) (tptr tuchar)) tuchar)
                    (Etempvar _t'4 tuchar))))))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
              (Tstruct _pr_sink noattr)) _len tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
              (Tstruct _pr_sink noattr)) _len tulong)
          (Ebinop Oadd (Etempvar _t'1 tulong) (Etempvar _m tulong) tulong))))))
|}.

Definition f_pr_a2ulabel := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tuchar)) :: (_n, tulong) ::
                (_k, (tptr (Tstruct _pr_sink noattr))) ::
                (_cps, (tptr tuint)) :: nil);
  fn_vars := ((_sep, tuchar) :: (_nul, tuchar) ::
              (_d, (Tstruct _pr_dec noattr)) :: (_u, (tarray tuchar 4)) ::
              nil);
  fn_temps := ((_st, tulong) :: (_e, tulong) :: (_m, tulong) ::
               (_j, tulong) :: (_ul, tulong) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tulong) :: (_t'1, tint) :: (_t'17, tuchar) ::
               (_t'16, tuchar) :: (_t'15, tuchar) :: (_t'14, tuchar) ::
               (_t'13, tuchar) :: (_t'12, tuchar) :: (_t'11, tuchar) ::
               (_t'10, tint) :: (_t'9, tulong) :: (_t'8, tuint) ::
               (_t'7, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sassign (Evar _sep tuchar) (Econst_int (Int.repr 46) tint))
    (Ssequence
      (Sassign (Evar _nul tuchar) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sloop
          (Ssequence
            Sskip
            (Ssequence
              (Sset _e (Etempvar _st tulong))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _e tulong)
                                     (Etempvar _n tulong) tint)
                        (Ssequence
                          (Sset _t'17
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Etempvar _e tulong) (tptr tuchar)) tuchar))
                          (Sset _t'1
                            (Ecast
                              (Ebinop One (Etempvar _t'17 tuchar)
                                (Econst_int (Int.repr 46) tint) tint) tbool)))
                        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                      (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
                    (Sset _e
                      (Ebinop Oadd (Etempvar _e tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  Sskip)
                (Ssequence
                  (Sset _m
                    (Ebinop Osub (Etempvar _e tulong) (Etempvar _st tulong)
                      tulong))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oge (Etempvar _m tulong)
                                           (Econst_int (Int.repr 4) tint)
                                           tint)
                              (Ssequence
                                (Sset _t'15
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Etempvar _st tulong) (tptr tuchar))
                                    tuchar))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'15 tuchar)
                                               (Econst_int (Int.repr 120) tint)
                                               tint)
                                  (Sset _t'3
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'16
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Etempvar _st tulong)
                                            (tptr tuchar)) tuchar))
                                      (Sset _t'3
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'16 tuchar)
                                            (Econst_int (Int.repr 88) tint)
                                            tint) tbool)))
                                    (Sset _t'3
                                      (Ecast (Etempvar _t'3 tint) tbool)))))
                              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _t'3 tint)
                              (Ssequence
                                (Sset _t'13
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Ebinop Oadd (Etempvar _st tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong) (tptr tuchar)) tuchar))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'13 tuchar)
                                               (Econst_int (Int.repr 110) tint)
                                               tint)
                                  (Sset _t'4
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'14
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Ebinop Oadd
                                              (Etempvar _st tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong) (tptr tuchar)) tuchar))
                                      (Sset _t'4
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'14 tuchar)
                                            (Econst_int (Int.repr 78) tint)
                                            tint) tbool)))
                                    (Sset _t'4
                                      (Ecast (Etempvar _t'4 tint) tbool)))))
                              (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'4 tint)
                            (Ssequence
                              (Sset _t'12
                                (Ederef
                                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                    (Ebinop Oadd (Etempvar _st tulong)
                                      (Econst_int (Int.repr 2) tint) tulong)
                                    (tptr tuchar)) tuchar))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _t'12 tuchar)
                                    (Econst_int (Int.repr 45) tint) tint)
                                  tbool)))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Sset _t'11
                              (Ederef
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Ebinop Oadd (Etempvar _st tulong)
                                    (Econst_int (Int.repr 3) tint) tulong)
                                  (tptr tuchar)) tuchar))
                            (Sset _t'6
                              (Ecast
                                (Ebinop Oeq (Etempvar _t'11 tuchar)
                                  (Econst_int (Int.repr 45) tint) tint)
                                tbool)))
                          (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'6 tint)
                        (Ssequence
                          (Sifthenelse (Ebinop Oge
                                         (Ebinop Osub (Etempvar _m tulong)
                                           (Econst_int (Int.repr 4) tint)
                                           tulong)
                                         (Econst_long (Int64.repr 4294967295) tulong)
                                         tint)
                            (Sreturn (Some (Eunop Oneg
                                             (Econst_int (Int.repr 1) tint)
                                             tint)))
                            Sskip)
                          (Ssequence
                            (Scall None
                              (Evar _pr_decode (Tfunction
                                                 ((tptr tuchar) :: tulong ::
                                                  (tptr tuint) :: tulong ::
                                                  (tptr (Tstruct _pr_dec noattr)) ::
                                                  nil) tvoid cc_default))
                              ((Ebinop Oadd
                                 (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                   (Etempvar _st tulong) (tptr tuchar))
                                 (Econst_int (Int.repr 4) tint)
                                 (tptr tuchar)) ::
                               (Ebinop Osub (Etempvar _m tulong)
                                 (Econst_int (Int.repr 4) tint) tulong) ::
                               (Etempvar _cps (tptr tuint)) ::
                               (Econst_int (Int.repr 512) tint) ::
                               (Eaddrof (Evar _d (Tstruct _pr_dec noattr))
                                 (tptr (Tstruct _pr_dec noattr))) :: nil))
                            (Ssequence
                              (Ssequence
                                (Sset _t'10
                                  (Efield (Evar _d (Tstruct _pr_dec noattr))
                                    _ok tint))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _t'10 tint) tint)
                                  (Sreturn (Some (Eunop Oneg
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)))
                                  Sskip))
                              (Ssequence
                                (Sset _j
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tulong))
                                (Sloop
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Evar _d (Tstruct _pr_dec noattr))
                                          _count tulong))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _j tulong)
                                                     (Etempvar _t'9 tulong)
                                                     tint)
                                        Sskip
                                        Sbreak))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _cps (tptr tuint))
                                                (Etempvar _j tulong)
                                                (tptr tuint)) tuint))
                                          (Scall (Some _t'2)
                                            (Evar _pr_utf8 (Tfunction
                                                             (tulong ::
                                                              (tptr tuchar) ::
                                                              nil) tulong
                                                             cc_default))
                                            ((Etempvar _t'8 tuint) ::
                                             (Evar _u (tarray tuchar 4)) ::
                                             nil)))
                                        (Sset _ul (Etempvar _t'2 tulong)))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _ul tulong)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Sreturn (Some (Eunop Oneg
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)))
                                          Sskip)
                                        (Scall None
                                          (Evar _pr_put (Tfunction
                                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                                           (Evar _u (tarray tuchar 4)) ::
                                           (Etempvar _ul tulong) :: nil)))))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))))))
                        (Scall None
                          (Evar _pr_put (Tfunction
                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                           (tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                           (Ebinop Oadd (Etempvar _s (tptr tuchar))
                             (Etempvar _st tulong) (tptr tuchar)) ::
                           (Etempvar _m tulong) :: nil))))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _e tulong)
                                     (Etempvar _n tulong) tint)
                        Sbreak
                        Sskip)
                      (Ssequence
                        (Scall None
                          (Evar _pr_put (Tfunction
                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                           (tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                           (Eaddrof (Evar _sep tuchar) (tptr tuchar)) ::
                           (Econst_int (Int.repr 1) tint) :: nil))
                        (Sset _st
                          (Ebinop Oadd (Etempvar _e tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))))))))
          Sskip)
        (Ssequence
          (Scall None
            (Evar _pr_put (Tfunction
                            ((tptr (Tstruct _pr_sink noattr)) ::
                             (tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
            ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
             (Eaddrof (Evar _nul tuchar) (tptr tuchar)) ::
             (Econst_int (Int.repr 1) tint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
                    (Tstruct _pr_sink noattr)) _short_ tint))
              (Sifthenelse (Etempvar _t'7 tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))
|}.

Definition v_ossl_shim_fail_next := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_ossl_shim_zalloc_failed := {|
  gvar_info := tint;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_ossl_shim_live := {|
  gvar_info := tlong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_copy_bytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_s, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
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
            (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar) (Etempvar _t'1 tuchar))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_same_bytes := {|
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

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_k, (Tstruct _pr_sink noattr)) :: nil);
  fn_temps := ((_n, tulong) :: (_in, (tptr tuchar)) ::
               (_snap, (tptr tuchar)) :: (_cps, (tptr tuint)) ::
               (_sl, tulong) :: (_outlen, tulong) :: (_mode, tuchar) ::
               (_out, (tptr tuchar)) :: (_want, (tptr tuchar)) ::
               (_r, tint) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, (tptr tvoid)) ::
               (_t'9, (tptr tvoid)) :: (_t'8, tuchar) :: (_t'7, tulong) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: (_t'20, tuchar) :: (_t'19, tint) ::
               (_t'18, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _nondet_size (Tfunction nil tulong cc_default)) nil)
      (Sset _n (Etempvar _t'1 tulong)))
    (Ssequence
      (Scall None
        (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
        ((Ebinop Olt (Etempvar _n tulong)
           (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tulong)
           tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                       cc_default))
            ((Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 1) tint)
               tulong) :: nil))
          (Sset _in (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                         (tptr tvoid) cc_default))
              ((Ebinop Oadd (Etempvar _n tulong)
                 (Econst_int (Int.repr 1) tint) tulong) :: nil))
            (Sset _snap (Etempvar _t'3 (tptr tvoid))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                           (tptr tvoid) cc_default))
                ((Ebinop Omul (Econst_int (Int.repr 512) tint)
                   (Esizeof tuint tulong) tulong) :: nil))
              (Sset _cps (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _in (tptr tuchar))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Sset _t'5 (Econst_int (Int.repr 1) tint))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oeq (Etempvar _snap (tptr tuchar))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                          tint) tbool)))
                  (Sifthenelse (Etempvar _t'5 tint)
                    (Sset _t'6 (Econst_int (Int.repr 1) tint))
                    (Sset _t'6
                      (Ecast
                        (Ebinop Oeq (Etempvar _cps (tptr tuint))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                          tint) tbool))))
                (Sifthenelse (Etempvar _t'6 tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Scall None
                  (Evar _nondet_bytes (Tfunction
                                        ((tptr tuchar) :: tulong :: nil)
                                        tvoid cc_default))
                  ((Etempvar _in (tptr tuchar)) :: (Etempvar _n tulong) ::
                   nil))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _in (tptr tuchar))
                        (Etempvar _n tulong) (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Scall None
                      (Evar _copy_bytes (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tvoid cc_default))
                      ((Etempvar _snap (tptr tuchar)) ::
                       (Etempvar _in (tptr tuchar)) ::
                       (Ebinop Oadd (Etempvar _n tulong)
                         (Econst_int (Int.repr 1) tint) tulong) :: nil))
                    (Ssequence
                      (Sset _sl
                        (Ecast (Econst_int (Int.repr 0) tint) tulong))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Sset _t'20
                                (Ederef
                                  (Ebinop Oadd (Etempvar _snap (tptr tuchar))
                                    (Etempvar _sl tulong) (tptr tuchar))
                                  tuchar))
                              (Sifthenelse (Ebinop One
                                             (Etempvar _t'20 tuchar)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                Sskip
                                Sbreak))
                            (Sset _sl
                              (Ebinop Oadd (Etempvar _sl tulong)
                                (Econst_int (Int.repr 1) tint) tulong)))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'7)
                              (Evar _nondet_size (Tfunction nil tulong
                                                   cc_default)) nil)
                            (Sset _outlen (Etempvar _t'7 tulong)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'8)
                                (Evar _nondet_u8 (Tfunction nil tuchar
                                                   cc_default)) nil)
                              (Sset _mode
                                (Ecast (Etempvar _t'8 tuchar) tuchar)))
                            (Ssequence
                              (Sset _out
                                (Ecast (Econst_int (Int.repr 0) tint)
                                  (tptr tvoid)))
                              (Ssequence
                                (Sset _want
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)))
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Ebinop Oand
                                                   (Etempvar _mode tuchar)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'9)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Etempvar _outlen tulong) :: nil))
                                        (Sset _out
                                          (Etempvar _t'9 (tptr tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'10)
                                            (Evar _quickproof_malloc 
                                            (Tfunction (tulong :: nil)
                                              (tptr tvoid) cc_default))
                                            ((Etempvar _outlen tulong) ::
                                             nil))
                                          (Sset _want
                                            (Etempvar _t'10 (tptr tvoid))))
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _out (tptr tuchar))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              (Sset _t'11
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'11
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _want (tptr tuchar))
                                                    (Ecast
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tvoid)) tint)
                                                  tbool)))
                                            (Sifthenelse (Etempvar _t'11 tint)
                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                              Sskip))
                                          (Ssequence
                                            (Scall None
                                              (Evar _nondet_bytes (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _out (tptr tuchar)) ::
                                               (Etempvar _outlen tulong) ::
                                               nil))
                                            (Scall None
                                              (Evar _copy_bytes (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   nil) tvoid
                                                                  cc_default))
                                              ((Etempvar _want (tptr tuchar)) ::
                                               (Etempvar _out (tptr tuchar)) ::
                                               (Etempvar _outlen tulong) ::
                                               nil))))))
                                    Sskip)
                                  (Ssequence
                                    (Sassign (Evar _ossl_shim_fail_next tint)
                                      (Ebinop One
                                        (Ebinop Oand (Etempvar _mode tuchar)
                                          (Econst_int (Int.repr 2) tint)
                                          tint)
                                        (Econst_int (Int.repr 0) tint) tint))
                                    (Ssequence
                                      (Sassign
                                        (Evar _ossl_shim_zalloc_failed tint)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sassign (Evar _ossl_shim_live tlong)
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'12)
                                              (Evar _ossl_a2ulabel (Tfunction
                                                                    ((tptr tschar) ::
                                                                    (tptr tschar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                              ((Ecast
                                                 (Etempvar _in (tptr tuchar))
                                                 (tptr tschar)) ::
                                               (Ecast
                                                 (Etempvar _out (tptr tuchar))
                                                 (tptr tschar)) ::
                                               (Etempvar _outlen tulong) ::
                                               nil))
                                            (Sset _r (Etempvar _t'12 tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _out (tptr tuchar))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint)
                                                  (Sset _t'14
                                                    (Econst_int (Int.repr 1) tint))
                                                  (Sset _t'14
                                                    (Ecast
                                                      (Ebinop Oeq
                                                        (Etempvar _outlen tulong)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint) tbool)))
                                                (Sifthenelse (Etempvar _t'14 tint)
                                                  (Sset _t'15
                                                    (Econst_int (Int.repr 1) tint))
                                                  (Ssequence
                                                    (Sset _t'19
                                                      (Evar _ossl_shim_zalloc_failed tint))
                                                    (Sset _t'15
                                                      (Ecast
                                                        (Ebinop One
                                                          (Etempvar _t'19 tint)
                                                          (Econst_int (Int.repr 0) tint)
                                                          tint) tbool)))))
                                              (Sifthenelse (Etempvar _t'15 tint)
                                                (Scall None
                                                  (Evar _gp_assert (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Ebinop Oeq
                                                     (Etempvar _r tint)
                                                     (Eunop Oneg
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint) tint) :: nil))
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Evar _k (Tstruct _pr_sink noattr))
                                                      _buf (tptr tuchar))
                                                    (Etempvar _want (tptr tuchar)))
                                                  (Ssequence
                                                    (Sassign
                                                      (Efield
                                                        (Evar _k (Tstruct _pr_sink noattr))
                                                        _cap tulong)
                                                      (Etempvar _outlen tulong))
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Evar _k (Tstruct _pr_sink noattr))
                                                          _len tulong)
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Evar _k (Tstruct _pr_sink noattr))
                                                            _short_ tint)
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Ssequence
                                                          (Scall (Some _t'13)
                                                            (Evar _pr_a2ulabel 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong ::
                                                               (tptr (Tstruct _pr_sink noattr)) ::
                                                               (tptr tuint) ::
                                                               nil) tint
                                                              cc_default))
                                                            ((Etempvar _snap (tptr tuchar)) ::
                                                             (Etempvar _sl tulong) ::
                                                             (Eaddrof
                                                               (Evar _k (Tstruct _pr_sink noattr))
                                                               (tptr (Tstruct _pr_sink noattr))) ::
                                                             (Etempvar _cps (tptr tuint)) ::
                                                             nil))
                                                          (Scall None
                                                            (Evar _gp_assert 
                                                            (Tfunction
                                                              (tint :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Ebinop Oeq
                                                               (Etempvar _r tint)
                                                               (Etempvar _t'13 tint)
                                                               tint) :: nil)))))))))
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _out (tptr tuchar))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Ssequence
                                                  (Scall (Some _t'16)
                                                    (Evar _same_bytes 
                                                    (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                                    ((Etempvar _out (tptr tuchar)) ::
                                                     (Etempvar _want (tptr tuchar)) ::
                                                     (Etempvar _outlen tulong) ::
                                                     nil))
                                                  (Scall None
                                                    (Evar _gp_assert 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _t'16 tint) ::
                                                     nil)))
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'17)
                                                    (Evar _same_bytes 
                                                    (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                                    ((Etempvar _in (tptr tuchar)) ::
                                                     (Etempvar _snap (tptr tuchar)) ::
                                                     (Ebinop Oadd
                                                       (Etempvar _n tulong)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tulong) :: nil))
                                                  (Scall None
                                                    (Evar _gp_assert 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _t'17 tint) ::
                                                     nil)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'18
                                                      (Evar _ossl_shim_live tlong))
                                                    (Scall None
                                                      (Evar _gp_assert 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Ebinop Oeq
                                                         (Etempvar _t'18 tlong)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint) :: nil)))
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _pr_dec Struct
   (Member_plain _ok tint :: Member_plain _count tulong :: nil)
   noattr ::
 Composite _pr_sink Struct
   (Member_plain _buf (tptr tuchar) :: Member_plain _cap tulong ::
    Member_plain _len tulong :: Member_plain _short_ tint :: nil)
   noattr :: nil).

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
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
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
 (_pr_digit_value, Gfun(Internal f_pr_digit_value)) ::
 (_pr_threshold, Gfun(Internal f_pr_threshold)) ::
 (_pr_adapt, Gfun(Internal f_pr_adapt)) ::
 (_pr_decode, Gfun(Internal f_pr_decode)) ::
 (_pr_utf8, Gfun(Internal f_pr_utf8)) ::
 (_pr_put, Gfun(Internal f_pr_put)) ::
 (_pr_a2ulabel, Gfun(Internal f_pr_a2ulabel)) ::
 (_ossl_a2ulabel,
   Gfun(External (EF_external "ossl_a2ulabel"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr tschar) :: (tptr tschar) :: tulong :: nil) tint cc_default)) ::
 (_ossl_shim_fail_next, Gvar v_ossl_shim_fail_next) ::
 (_ossl_shim_zalloc_failed, Gvar v_ossl_shim_zalloc_failed) ::
 (_ossl_shim_live, Gvar v_ossl_shim_live) ::
 (_copy_bytes, Gfun(Internal f_copy_bytes)) ::
 (_same_bytes, Gfun(Internal f_same_bytes)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ossl_shim_live :: _ossl_shim_zalloc_failed ::
 _ossl_shim_fail_next :: _ossl_a2ulabel :: _gp_assume :: _gp_assert ::
 _nondet_bytes :: _nondet_size :: _nondet_u8 :: _quickproof_malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


