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
  Definition source_file := "crypto/punycode.c".
  Definition normalized := true.
End Info.

Definition _OPENSSL_strncasecmp : ident := $"OPENSSL_strncasecmp".
Definition _WPACKET_cleanup : ident := $"WPACKET_cleanup".
Definition _WPACKET_init_static_len : ident := $"WPACKET_init_static_len".
Definition _WPACKET_memcpy : ident := $"WPACKET_memcpy".
Definition _WPACKET_put_bytes__ : ident := $"WPACKET_put_bytes__".
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
Definition ___stringlit_punycode_1 : ident := $"__stringlit_punycode_1".
Definition _a : ident := $"a".
Definition _adapt : ident := $"adapt".
Definition _base : ident := $"base".
Definition _basic_count : ident := $"basic_count".
Definition _bias : ident := $"bias".
Definition _buf : ident := $"buf".
Definition _buf_mem_st : ident := $"buf_mem_st".
Definition _bufsize : ident := $"bufsize".
Definition _codepoint2utf8 : ident := $"codepoint2utf8".
Definition _curr : ident := $"curr".
Definition _damp : ident := $"damp".
Definition _data : ident := $"data".
Definition _delimiter : ident := $"delimiter".
Definition _delta : ident := $"delta".
Definition _digit : ident := $"digit".
Definition _digit_decoded : ident := $"digit_decoded".
Definition _enc_len : ident := $"enc_len".
Definition _endfirst : ident := $"endfirst".
Definition _firsttime : ident := $"firsttime".
Definition _flags : ident := $"flags".
Definition _gp_j : ident := $"gp_j".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _initial_bias : ident := $"initial_bias".
Definition _initial_n : ident := $"initial_n".
Definition _inptr : ident := $"inptr".
Definition _is_basic : ident := $"is_basic".
Definition _k : ident := $"k".
Definition _lenbytes : ident := $"lenbytes".
Definition _length : ident := $"length".
Definition _loop : ident := $"loop".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _max_out : ident := $"max_out".
Definition _maxint : ident := $"maxint".
Definition _maxsize : ident := $"maxsize".
Definition _n : ident := $"n".
Definition _numpoints : ident := $"numpoints".
Definition _oldi : ident := $"oldi".
Definition _ossl_a2ulabel : ident := $"ossl_a2ulabel".
Definition _ossl_punycode_decode : ident := $"ossl_punycode_decode".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _pDecoded : ident := $"pDecoded".
Definition _pEncoded : ident := $"pEncoded".
Definition _packet_len : ident := $"packet_len".
Definition _parent : ident := $"parent".
Definition _pkt : ident := $"pkt".
Definition _pout_length : ident := $"pout_length".
Definition _processed_in : ident := $"processed_in".
Definition _pwritten : ident := $"pwritten".
Definition _result : ident := $"result".
Definition _seed : ident := $"seed".
Definition _skew : ident := $"skew".
Definition _staticbuf : ident := $"staticbuf".
Definition _strchr : ident := $"strchr".
Definition _strlen : ident := $"strlen".
Definition _subs : ident := $"subs".
Definition _t : ident := $"t".
Definition _tmax : ident := $"tmax".
Definition _tmin : ident := $"tmin".
Definition _tmpptr : ident := $"tmpptr".
Definition _utf : ident := $"utf".
Definition _utfsize : ident := $"utfsize".
Definition _w : ident := $"w".
Definition _wpacket_st : ident := $"wpacket_st".
Definition _wpacket_sub : ident := $"wpacket_sub".
Definition _written : ident := $"written".
Definition _written_out : ident := $"written_out".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_punycode_1 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_base := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 36) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_tmin := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 1) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_tmax := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 26) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_skew := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 38) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_damp := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 700) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_initial_bias := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 72) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_initial_n := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 128) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_maxint := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr (-1)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_delimiter := {|
  gvar_info := tschar;
  gvar_init := (Init_int8 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_adapt := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_delta, tuint) :: (_numpoints, tuint) ::
                (_firsttime, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tuint) :: (_t'1, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _k (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sifthenelse (Etempvar _firsttime tuint)
        (Ssequence
          (Sset _t'11 (Evar _damp tuint))
          (Sset _t'1
            (Ecast
              (Ebinop Odiv (Etempvar _delta tuint) (Etempvar _t'11 tuint)
                tuint) tuint)))
        (Sset _t'1
          (Ecast
            (Ebinop Odiv (Etempvar _delta tuint)
              (Econst_int (Int.repr 2) tint) tuint) tuint)))
      (Sset _delta (Etempvar _t'1 tuint)))
    (Ssequence
      (Sset _delta
        (Ebinop Oadd (Etempvar _delta tuint)
          (Ebinop Odiv (Etempvar _delta tuint) (Etempvar _numpoints tuint)
            tuint) tuint))
      (Ssequence
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'8 (Evar _base tuint))
              (Ssequence
                (Sset _t'9 (Evar _tmin tuint))
                (Ssequence
                  (Sset _t'10 (Evar _tmax tuint))
                  (Sifthenelse (Ebinop Ogt (Etempvar _delta tuint)
                                 (Ebinop Odiv
                                   (Ebinop Omul
                                     (Ebinop Osub (Etempvar _t'8 tuint)
                                       (Etempvar _t'9 tuint) tuint)
                                     (Etempvar _t'10 tuint) tuint)
                                   (Econst_int (Int.repr 2) tint) tuint)
                                 tint)
                    Sskip
                    Sbreak))))
            (Ssequence
              (Ssequence
                (Sset _t'6 (Evar _base tuint))
                (Ssequence
                  (Sset _t'7 (Evar _tmin tuint))
                  (Sset _delta
                    (Ebinop Odiv (Etempvar _delta tuint)
                      (Ebinop Osub (Etempvar _t'6 tuint)
                        (Etempvar _t'7 tuint) tuint) tuint))))
              (Ssequence
                (Sset _t'5 (Evar _base tuint))
                (Sset _k
                  (Ebinop Oadd (Etempvar _k tuint) (Etempvar _t'5 tuint)
                    tuint)))))
          Sskip)
        (Ssequence
          (Sset _t'2 (Evar _base tuint))
          (Ssequence
            (Sset _t'3 (Evar _tmin tuint))
            (Ssequence
              (Sset _t'4 (Evar _skew tuint))
              (Sreturn (Some (Ebinop Oadd (Etempvar _k tuint)
                               (Ebinop Odiv
                                 (Ebinop Omul
                                   (Ebinop Oadd
                                     (Ebinop Osub (Etempvar _t'2 tuint)
                                       (Etempvar _t'3 tuint) tuint)
                                     (Econst_int (Int.repr 1) tint) tuint)
                                   (Etempvar _delta tuint) tuint)
                                 (Ebinop Oadd (Etempvar _delta tuint)
                                   (Etempvar _t'4 tuint) tuint) tuint) tuint))))))))))
|}.

Definition f_is_basic := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _a tuint)
                 (Econst_int (Int.repr 128) tint) tint)
    (Sset _t'1 (Ecast (Econst_int (Int.repr 1) tint) tint))
    (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_digit_decoded := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _a tuchar)
                   (Econst_int (Int.repr 65) tint) tint)
      (Sset _t'1
        (Ecast
          (Ebinop Ole (Etempvar _a tuchar) (Econst_int (Int.repr 90) tint)
            tint) tbool))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ebinop Osub (Etempvar _a tuchar)
                       (Econst_int (Int.repr 65) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _a tuchar)
                     (Econst_int (Int.repr 97) tint) tint)
        (Sset _t'2
          (Ecast
            (Ebinop Ole (Etempvar _a tuchar) (Econst_int (Int.repr 122) tint)
              tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sreturn (Some (Ebinop Osub (Etempvar _a tuchar)
                         (Econst_int (Int.repr 97) tint) tint)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _a tuchar)
                       (Econst_int (Int.repr 48) tint) tint)
          (Sset _t'3
            (Ecast
              (Ebinop Ole (Etempvar _a tuchar)
                (Econst_int (Int.repr 57) tint) tint) tbool))
          (Sset _t'3 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'3 tint)
          (Sreturn (Some (Ebinop Oadd
                           (Ebinop Osub (Etempvar _a tuchar)
                             (Econst_int (Int.repr 48) tint) tint)
                           (Econst_int (Int.repr 26) tint) tint)))
          Sskip))
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))))
|}.

Definition f_ossl_punycode_decode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pEncoded, (tptr tschar)) :: (_enc_len, tulong) ::
                (_pDecoded, (tptr tuint)) :: (_pout_length, (tptr tuint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_i, tuint) :: (_bias, tuint) ::
               (_processed_in, tuint) :: (_written_out, tuint) ::
               (_max_out, tuint) :: (_basic_count, tuint) ::
               (_loop, tuint) :: (_oldi, tuint) :: (_w, tuint) ::
               (_k, tuint) :: (_t, tuint) :: (_digit, tint) ::
               (_gp_j, tuint) :: (_t'4, tint) :: (_t'3, tuint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'19, tschar) ::
               (_t'18, tschar) :: (_t'17, tschar) :: (_t'16, tschar) ::
               (_t'15, tschar) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Evar _initial_n tuint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _bias (Evar _initial_bias tuint))
      (Ssequence
        (Sset _processed_in (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _written_out (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sset _max_out
              (Ederef (Etempvar _pout_length (tptr tuint)) tuint))
            (Ssequence
              (Sset _basic_count (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sifthenelse (Ebinop Oge (Etempvar _enc_len tulong)
                               (Ebinop Oadd
                                 (Ebinop Omul
                                   (Econst_int (Int.repr 2147483647) tint)
                                   (Econst_int (Int.repr 2) tuint) tuint)
                                 (Econst_int (Int.repr 1) tuint) tuint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Sset _loop (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _loop tuint)
                                       (Ecast (Etempvar _enc_len tulong)
                                         tuint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _t'18
                            (Ederef
                              (Ebinop Oadd (Etempvar _pEncoded (tptr tschar))
                                (Etempvar _loop tuint) (tptr tschar)) tschar))
                          (Ssequence
                            (Sset _t'19 (Evar _delimiter tschar))
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'18 tschar)
                                           (Etempvar _t'19 tschar) tint)
                              (Sset _basic_count (Etempvar _loop tuint))
                              Sskip))))
                      (Sset _loop
                        (Ebinop Oadd (Etempvar _loop tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Sifthenelse (Ebinop Ogt (Etempvar _basic_count tuint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sifthenelse (Ebinop Ogt
                                       (Etempvar _basic_count tuint)
                                       (Etempvar _max_out tuint) tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Sset _loop (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _loop tuint)
                                               (Etempvar _basic_count tuint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'17
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _pEncoded (tptr tschar))
                                            (Etempvar _loop tuint)
                                            (tptr tschar)) tschar))
                                      (Scall (Some _t'1)
                                        (Evar _is_basic (Tfunction
                                                          (tuint :: nil) tint
                                                          cc_default))
                                        ((Etempvar _t'17 tschar) :: nil)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'1 tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'16
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _pEncoded (tptr tschar))
                                            (Etempvar _loop tuint)
                                            (tptr tschar)) tschar))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _pDecoded (tptr tuint))
                                            (Etempvar _loop tuint)
                                            (tptr tuint)) tuint)
                                        (Etempvar _t'16 tschar)))
                                    (Sset _written_out
                                      (Ebinop Oadd
                                        (Etempvar _written_out tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))))
                              (Sset _loop
                                (Ebinop Oadd (Etempvar _loop tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Sset _processed_in
                            (Ebinop Oadd (Etempvar _basic_count tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      Sskip)
                    (Ssequence
                      (Ssequence
                        (Sset _loop (Etempvar _processed_in tuint))
                        (Swhile
                          (Ebinop Olt (Etempvar _loop tuint)
                            (Ecast (Etempvar _enc_len tulong) tuint) tint)
                          (Ssequence
                            (Sset _oldi (Etempvar _i tuint))
                            (Ssequence
                              (Sset _w (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Ssequence
                                  (Sset _k (Evar _base tuint))
                                  (Sloop
                                    (Ssequence
                                      Sskip
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oge
                                                       (Etempvar _loop tuint)
                                                       (Etempvar _enc_len tulong)
                                                       tint)
                                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                          Sskip)
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'15
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _pEncoded (tptr tschar))
                                                    (Etempvar _loop tuint)
                                                    (tptr tschar)) tschar))
                                              (Scall (Some _t'2)
                                                (Evar _digit_decoded 
                                                (Tfunction (tuchar :: nil)
                                                  tint cc_default))
                                                ((Etempvar _t'15 tschar) ::
                                                 nil)))
                                            (Sset _digit
                                              (Etempvar _t'2 tint)))
                                          (Ssequence
                                            (Sset _loop
                                              (Ebinop Oadd
                                                (Etempvar _loop tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint))
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _digit tint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                Sskip)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'14
                                                    (Evar _maxint tuint))
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Ecast
                                                                   (Etempvar _digit tint)
                                                                   tuint)
                                                                 (Ebinop Odiv
                                                                   (Ebinop Osub
                                                                    (Etempvar _t'14 tuint)
                                                                    (Etempvar _i tuint)
                                                                    tuint)
                                                                   (Etempvar _w tuint)
                                                                   tuint)
                                                                 tint)
                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                    Sskip))
                                                (Ssequence
                                                  (Sset _i
                                                    (Ebinop Oadd
                                                      (Etempvar _i tuint)
                                                      (Ebinop Omul
                                                        (Etempvar _digit tint)
                                                        (Etempvar _w tuint)
                                                        tuint) tuint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Ole
                                                                    (Etempvar _k tuint)
                                                                    (Etempvar _bias tuint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _t'13
                                                            (Evar _tmin tuint))
                                                          (Sset _t'3
                                                            (Ecast
                                                              (Etempvar _t'13 tuint)
                                                              tuint)))
                                                        (Ssequence
                                                          (Sset _t'11
                                                            (Evar _tmax tuint))
                                                          (Sifthenelse 
                                                            (Ebinop Oge
                                                              (Etempvar _k tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _bias tuint)
                                                                (Etempvar _t'11 tuint)
                                                                tuint) tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'12
                                                                  (Evar _tmax tuint))
                                                                (Sset _t'3
                                                                  (Ecast
                                                                    (Etempvar _t'12 tuint)
                                                                    tuint)))
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Etempvar _t'3 tuint)
                                                                  tuint)))
                                                            (Ssequence
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Ebinop Osub
                                                                    (Etempvar _k tuint)
                                                                    (Etempvar _bias tuint)
                                                                    tuint)
                                                                  tuint))
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Etempvar _t'3 tuint)
                                                                  tuint))))))
                                                      (Sset _t
                                                        (Etempvar _t'3 tuint)))
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _digit tint)
                                                                    tuint)
                                                                    (Etempvar _t tuint)
                                                                    tint)
                                                        Sbreak
                                                        Sskip)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'9
                                                            (Evar _maxint tuint))
                                                          (Ssequence
                                                            (Sset _t'10
                                                              (Evar _base tuint))
                                                            (Sifthenelse 
                                                              (Ebinop Ogt
                                                                (Etempvar _w tuint)
                                                                (Ebinop Odiv
                                                                  (Etempvar _t'9 tuint)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'10 tuint)
                                                                    (Etempvar _t tuint)
                                                                    tuint)
                                                                  tuint)
                                                                tint)
                                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                              Sskip)))
                                                        (Ssequence
                                                          (Sset _t'8
                                                            (Evar _base tuint))
                                                          (Sset _w
                                                            (Ebinop Omul
                                                              (Etempvar _w tuint)
                                                              (Ebinop Osub
                                                                (Etempvar _t'8 tuint)
                                                                (Etempvar _t tuint)
                                                                tuint) tuint)))))))))))))
                                    (Ssequence
                                      (Sset _t'7 (Evar _base tuint))
                                      (Sset _k
                                        (Ebinop Oadd (Etempvar _k tuint)
                                          (Etempvar _t'7 tuint) tuint)))))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'4)
                                      (Evar _adapt (Tfunction
                                                     (tuint :: tuint ::
                                                      tuint :: nil) tint
                                                     cc_default))
                                      ((Ebinop Osub (Etempvar _i tuint)
                                         (Etempvar _oldi tuint) tuint) ::
                                       (Ebinop Oadd
                                         (Etempvar _written_out tuint)
                                         (Econst_int (Int.repr 1) tint)
                                         tuint) ::
                                       (Ebinop Oeq (Etempvar _oldi tuint)
                                         (Econst_int (Int.repr 0) tint) tint) ::
                                       nil))
                                    (Sset _bias (Etempvar _t'4 tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'6 (Evar _maxint tuint))
                                      (Sifthenelse (Ebinop Ogt
                                                     (Ebinop Odiv
                                                       (Etempvar _i tuint)
                                                       (Ebinop Oadd
                                                         (Etempvar _written_out tuint)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tuint) tuint)
                                                     (Ebinop Osub
                                                       (Etempvar _t'6 tuint)
                                                       (Etempvar _n tuint)
                                                       tuint) tint)
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                        Sskip))
                                    (Ssequence
                                      (Sset _n
                                        (Ebinop Oadd (Etempvar _n tuint)
                                          (Ebinop Odiv (Etempvar _i tuint)
                                            (Ebinop Oadd
                                              (Etempvar _written_out tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint) tuint) tuint))
                                      (Ssequence
                                        (Sset _i
                                          (Ebinop Omod (Etempvar _i tuint)
                                            (Ebinop Oadd
                                              (Etempvar _written_out tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint) tuint))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oge
                                                         (Etempvar _written_out tuint)
                                                         (Etempvar _max_out tuint)
                                                         tint)
                                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                            Sskip)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _gp_j
                                                (Etempvar _written_out tuint))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Etempvar _gp_j tuint)
                                                                 (Etempvar _i tuint)
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sset _t'5
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _pDecoded (tptr tuint))
                                                          (Ebinop Osub
                                                            (Etempvar _gp_j tuint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _pDecoded (tptr tuint))
                                                          (Etempvar _gp_j tuint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'5 tuint))))
                                                (Sset _gp_j
                                                  (Ebinop Osub
                                                    (Etempvar _gp_j tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _pDecoded (tptr tuint))
                                                    (Etempvar _i tuint)
                                                    (tptr tuint)) tuint)
                                                (Etempvar _n tuint))
                                              (Ssequence
                                                (Sset _i
                                                  (Ebinop Oadd
                                                    (Etempvar _i tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))
                                                (Sset _written_out
                                                  (Ebinop Oadd
                                                    (Etempvar _written_out tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint)))))))))))))))
                      (Ssequence
                        (Sassign
                          (Ederef (Etempvar _pout_length (tptr tuint)) tuint)
                          (Etempvar _written_out tuint))
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))))))
|}.

Definition f_codepoint2utf8 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_utf, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ole (Etempvar _utf tulong)
               (Econst_int (Int.repr 127) tint) tint)
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _out (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ecast (Etempvar _utf tulong) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _out (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
  (Sifthenelse (Ebinop Ole (Etempvar _utf tulong)
                 (Econst_int (Int.repr 2047) tint) tint)
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _out (tptr tuchar))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oor
            (Ebinop Oand
              (Ebinop Oshr (Etempvar _utf tulong)
                (Econst_int (Int.repr 6) tint) tulong)
              (Econst_int (Int.repr 31) tint) tulong)
            (Econst_int (Int.repr 192) tint) tulong) tuchar))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _out (tptr tuchar))
              (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oor
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _utf tulong)
                  (Econst_int (Int.repr 0) tint) tulong)
                (Econst_int (Int.repr 63) tint) tulong)
              (Econst_int (Int.repr 128) tint) tulong) tuchar))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Econst_int (Int.repr 2) tint))))))
    (Sifthenelse (Ebinop Ole (Etempvar _utf tulong)
                   (Econst_int (Int.repr 65535) tint) tint)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _out (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oor
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _utf tulong)
                  (Econst_int (Int.repr 12) tint) tulong)
                (Econst_int (Int.repr 15) tint) tulong)
              (Econst_int (Int.repr 224) tint) tulong) tuchar))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oor
                (Ebinop Oand
                  (Ebinop Oshr (Etempvar _utf tulong)
                    (Econst_int (Int.repr 6) tint) tulong)
                  (Econst_int (Int.repr 63) tint) tulong)
                (Econst_int (Int.repr 128) tint) tulong) tuchar))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                  (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oor
                  (Ebinop Oand
                    (Ebinop Oshr (Etempvar _utf tulong)
                      (Econst_int (Int.repr 0) tint) tulong)
                    (Econst_int (Int.repr 63) tint) tulong)
                  (Econst_int (Int.repr 128) tint) tulong) tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _out (tptr tuchar))
                    (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Econst_int (Int.repr 3) tint)))))))
      (Sifthenelse (Ebinop Ole (Etempvar _utf tulong)
                     (Econst_int (Int.repr 1114111) tint) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oor
                (Ebinop Oand
                  (Ebinop Oshr (Etempvar _utf tulong)
                    (Econst_int (Int.repr 18) tint) tulong)
                  (Econst_int (Int.repr 7) tint) tulong)
                (Econst_int (Int.repr 240) tint) tulong) tuchar))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oor
                  (Ebinop Oand
                    (Ebinop Oshr (Etempvar _utf tulong)
                      (Econst_int (Int.repr 12) tint) tulong)
                    (Econst_int (Int.repr 63) tint) tulong)
                  (Econst_int (Int.repr 128) tint) tulong) tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _out (tptr tuchar))
                    (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oor
                    (Ebinop Oand
                      (Ebinop Oshr (Etempvar _utf tulong)
                        (Econst_int (Int.repr 6) tint) tulong)
                      (Econst_int (Int.repr 63) tint) tulong)
                    (Econst_int (Int.repr 128) tint) tulong) tuchar))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuchar))
                      (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                  (Ecast
                    (Ebinop Oor
                      (Ebinop Oand
                        (Ebinop Oshr (Etempvar _utf tulong)
                          (Econst_int (Int.repr 0) tint) tulong)
                        (Econst_int (Int.repr 63) tint) tulong)
                      (Econst_int (Int.repr 128) tint) tulong) tuchar))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _out (tptr tuchar))
                        (Econst_int (Int.repr 4) tint) (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 0) tint))
                  (Sreturn (Some (Econst_int (Int.repr 4) tint))))))))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Ecast (Econst_int (Int.repr 239) tint) tuchar))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Ecast (Econst_int (Int.repr 191) tint) tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _out (tptr tuchar))
                    (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                (Ecast (Econst_int (Int.repr 189) tint) tuchar))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuchar))
                      (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                  (Econst_int (Int.repr 0) tint))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_ossl_a2ulabel := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tschar)) :: (_out, (tptr tschar)) ::
                (_outlen, tulong) :: nil);
  fn_vars := ((_buf, (tarray tuint 512)) ::
              (_pkt, (Tstruct _wpacket_st noattr)) :: (_bufsize, tuint) ::
              (_seed, (tarray tuchar 6)) :: nil);
  fn_temps := ((_inptr, (tptr tschar)) :: (_result, tint) :: (_i, tuint) ::
               (_tmpptr, (tptr tschar)) :: (_delta, tulong) ::
               (_utfsize, tulong) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, (tptr tschar)) ::
               (_t'1, tint) :: (_t'14, tuint) :: (_t'13, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _inptr (Etempvar _in (tptr tschar)))
  (Ssequence
    (Sset _result (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Ebinop One
                       (Ebinop One (Etempvar _out (tptr tschar))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint) (Econst_int (Int.repr 0) tint) tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _WPACKET_init_static_len (Tfunction
                                             ((tptr (Tstruct _wpacket_st noattr)) ::
                                              (tptr tuchar) :: tulong ::
                                              tulong :: nil) tint cc_default))
            ((Eaddrof (Evar _pkt (Tstruct _wpacket_st noattr))
               (tptr (Tstruct _wpacket_st noattr))) ::
             (Ecast (Etempvar _out (tptr tschar)) (tptr tuchar)) ::
             (Etempvar _outlen tulong) :: (Econst_int (Int.repr 0) tint) ::
             nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
            Sskip))
        (Ssequence
          (Sloop
            (Ssequence
              Sskip
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _strchr (Tfunction ((tptr tschar) :: tint :: nil)
                                    (tptr tschar) cc_default))
                    ((Etempvar _inptr (tptr tschar)) ::
                     (Econst_int (Int.repr 46) tint) :: nil))
                  (Sset _tmpptr (Etempvar _t'2 (tptr tschar))))
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _tmpptr (tptr tschar))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Sset _t'3
                        (Ecast
                          (Ecast
                            (Ebinop Osub (Etempvar _tmpptr (tptr tschar))
                              (Etempvar _inptr (tptr tschar)) tlong) tulong)
                          tulong))
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _strlen (Tfunction ((tptr tschar) :: nil)
                                          tulong cc_default))
                          ((Etempvar _inptr (tptr tschar)) :: nil))
                        (Sset _t'3 (Ecast (Etempvar _t'4 tulong) tulong))))
                    (Sset _delta (Etempvar _t'3 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _OPENSSL_strncasecmp (Tfunction
                                                     ((tptr tschar) ::
                                                      (tptr tschar) ::
                                                      tulong :: nil) tint
                                                     cc_default))
                        ((Etempvar _inptr (tptr tschar)) ::
                         (Evar ___stringlit_punycode_1 (tarray tschar 5)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 5) tulong)
                           (Econst_int (Int.repr 1) tint) tulong) :: nil))
                      (Sifthenelse (Eunop Onotbool
                                     (Ebinop Oeq (Etempvar _t'9 tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                                     tint)
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _WPACKET_memcpy (Tfunction
                                                    ((tptr (Tstruct _wpacket_st noattr)) ::
                                                     (tptr tvoid) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                            ((Eaddrof
                               (Evar _pkt (Tstruct _wpacket_st noattr))
                               (tptr (Tstruct _wpacket_st noattr))) ::
                             (Etempvar _inptr (tptr tschar)) ::
                             (Etempvar _delta tulong) :: nil))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'5 tint)
                                         tint)
                            (Sset _result (Econst_int (Int.repr 0) tint))
                            Sskip))
                        (Ssequence
                          (Sassign (Evar _bufsize tuint)
                            (Econst_int (Int.repr 512) tint))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar _ossl_punycode_decode (Tfunction
                                                              ((tptr tschar) ::
                                                               tulong ::
                                                               (tptr tuint) ::
                                                               (tptr tuint) ::
                                                               nil) tint
                                                              cc_default))
                                ((Ebinop Oadd (Etempvar _inptr (tptr tschar))
                                   (Econst_int (Int.repr 4) tint)
                                   (tptr tschar)) ::
                                 (Ebinop Osub (Etempvar _delta tulong)
                                   (Econst_int (Int.repr 4) tint) tulong) ::
                                 (Evar _buf (tarray tuint 512)) ::
                                 (Eaddrof (Evar _bufsize tuint) (tptr tuint)) ::
                                 nil))
                              (Sifthenelse (Ebinop Ole (Etempvar _t'6 tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _result
                                    (Eunop Oneg
                                      (Econst_int (Int.repr 1) tint) tint))
                                  Sbreak)
                                Sskip))
                            (Ssequence
                              (Ssequence
                                (Sset _i (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'14 (Evar _bufsize tuint))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tuint)
                                                     (Etempvar _t'14 tuint)
                                                     tint)
                                        Sskip
                                        Sbreak))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'13
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _buf (tarray tuint 512))
                                                (Etempvar _i tuint)
                                                (tptr tuint)) tuint))
                                          (Scall (Some _t'7)
                                            (Evar _codepoint2utf8 (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                            ((Evar _seed (tarray tuchar 6)) ::
                                             (Etempvar _t'13 tuint) :: nil)))
                                        (Sset _utfsize
                                          (Ecast (Etempvar _t'7 tint) tulong)))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _utfsize tulong)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _result
                                              (Eunop Oneg
                                                (Econst_int (Int.repr 1) tint)
                                                tint))
                                            Sbreak)
                                          Sskip)
                                        (Ssequence
                                          (Scall (Some _t'8)
                                            (Evar _WPACKET_memcpy (Tfunction
                                                                    ((tptr (Tstruct _wpacket_st noattr)) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                            ((Eaddrof
                                               (Evar _pkt (Tstruct _wpacket_st noattr))
                                               (tptr (Tstruct _wpacket_st noattr))) ::
                                             (Evar _seed (tarray tuchar 6)) ::
                                             (Etempvar _utfsize tulong) ::
                                             nil))
                                          (Sifthenelse (Eunop Onotbool
                                                         (Etempvar _t'8 tint)
                                                         tint)
                                            (Sset _result
                                              (Econst_int (Int.repr 0) tint))
                                            Sskip)))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _result tint)
                                             (Eunop Oneg
                                               (Econst_int (Int.repr 1) tint)
                                               tint) tint)
                                Sbreak
                                Sskip))))))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _tmpptr (tptr tschar))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        Sbreak
                        Sskip)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _WPACKET_put_bytes__ (Tfunction
                                                         ((tptr (Tstruct _wpacket_st noattr)) ::
                                                          tulong :: tulong ::
                                                          nil) tint
                                                         cc_default))
                            ((Eaddrof
                               (Evar _pkt (Tstruct _wpacket_st noattr))
                               (tptr (Tstruct _wpacket_st noattr))) ::
                             (Econst_int (Int.repr 46) tint) ::
                             (Econst_int (Int.repr 1) tint) :: nil))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'10 tint)
                                         tint)
                            (Sset _result (Econst_int (Int.repr 0) tint))
                            Sskip))
                        (Sset _inptr
                          (Ebinop Oadd (Etempvar _tmpptr (tptr tschar))
                            (Econst_int (Int.repr 1) tint) (tptr tschar)))))))))
            Sskip)
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _result tint)
                             (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                             tint)
                (Ssequence
                  (Scall (Some _t'12)
                    (Evar _WPACKET_put_bytes__ (Tfunction
                                                 ((tptr (Tstruct _wpacket_st noattr)) ::
                                                  tulong :: tulong :: nil)
                                                 tint cc_default))
                    ((Eaddrof (Evar _pkt (Tstruct _wpacket_st noattr))
                       (tptr (Tstruct _wpacket_st noattr))) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 1) tint) :: nil))
                  (Sset _t'11
                    (Ecast (Eunop Onotbool (Etempvar _t'12 tint) tint) tbool)))
                (Sset _t'11 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'11 tint)
                (Sset _result (Econst_int (Int.repr 0) tint))
                Sskip))
            (Ssequence
              (Scall None
                (Evar _WPACKET_cleanup (Tfunction
                                         ((tptr (Tstruct _wpacket_st noattr)) ::
                                          nil) tvoid cc_default))
                ((Eaddrof (Evar _pkt (Tstruct _wpacket_st noattr))
                   (tptr (Tstruct _wpacket_st noattr))) :: nil))
              (Sreturn (Some (Etempvar _result tint))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _buf_mem_st Struct
   (Member_plain _length tulong :: Member_plain _data (tptr tschar) ::
    Member_plain _max tulong :: Member_plain _flags tulong :: nil)
   noattr ::
 Composite _wpacket_sub Struct
   (Member_plain _parent (tptr (Tstruct _wpacket_sub noattr)) ::
    Member_plain _packet_len tulong :: Member_plain _lenbytes tulong ::
    Member_plain _pwritten tulong :: Member_plain _flags tuint :: nil)
   noattr ::
 Composite _wpacket_st Struct
   (Member_plain _buf (tptr (Tstruct _buf_mem_st noattr)) ::
    Member_plain _staticbuf (tptr tuchar) :: Member_plain _curr tulong ::
    Member_plain _written tulong :: Member_plain _maxsize tulong ::
    Member_plain _subs (tptr (Tstruct _wpacket_sub noattr)) ::
    Member_plain _endfirst tuint :: nil)
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
     cc_default)) :: (___stringlit_punycode_1, Gvar v___stringlit_punycode_1) ::
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
 (_strchr,
   Gfun(External (EF_external "strchr"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xptr
                     cc_default)) ((tptr tschar) :: tint :: nil)
     (tptr tschar) cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tschar) :: nil) tulong cc_default)) ::
 (_OPENSSL_strncasecmp,
   Gfun(External (EF_external "OPENSSL_strncasecmp"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr tschar) :: (tptr tschar) :: tulong :: nil) tint cc_default)) ::
 (_WPACKET_init_static_len,
   Gfun(External (EF_external "WPACKET_init_static_len"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _wpacket_st noattr)) :: (tptr tuchar) :: tulong ::
      tulong :: nil) tint cc_default)) ::
 (_WPACKET_put_bytes__,
   Gfun(External (EF_external "WPACKET_put_bytes__"
                   (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _wpacket_st noattr)) :: tulong :: tulong :: nil) tint
     cc_default)) ::
 (_WPACKET_memcpy,
   Gfun(External (EF_external "WPACKET_memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _wpacket_st noattr)) :: (tptr tvoid) :: tulong :: nil)
     tint cc_default)) ::
 (_WPACKET_cleanup,
   Gfun(External (EF_external "WPACKET_cleanup"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _wpacket_st noattr)) :: nil) tvoid cc_default)) ::
 (_base, Gvar v_base) :: (_tmin, Gvar v_tmin) :: (_tmax, Gvar v_tmax) ::
 (_skew, Gvar v_skew) :: (_damp, Gvar v_damp) ::
 (_initial_bias, Gvar v_initial_bias) :: (_initial_n, Gvar v_initial_n) ::
 (_maxint, Gvar v_maxint) :: (_delimiter, Gvar v_delimiter) ::
 (_adapt, Gfun(Internal f_adapt)) ::
 (_is_basic, Gfun(Internal f_is_basic)) ::
 (_digit_decoded, Gfun(Internal f_digit_decoded)) ::
 (_ossl_punycode_decode, Gfun(Internal f_ossl_punycode_decode)) ::
 (_codepoint2utf8, Gfun(Internal f_codepoint2utf8)) ::
 (_ossl_a2ulabel, Gfun(Internal f_ossl_a2ulabel)) :: nil).

Definition public_idents : list ident :=
(_ossl_a2ulabel :: _ossl_punycode_decode :: _WPACKET_cleanup ::
 _WPACKET_memcpy :: _WPACKET_put_bytes__ :: _WPACKET_init_static_len ::
 _OPENSSL_strncasecmp :: _strlen :: _strchr :: ___builtin_debug ::
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


