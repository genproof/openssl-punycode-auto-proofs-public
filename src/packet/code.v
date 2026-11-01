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
  Definition source_file := "patch/units/packet_ext.c".
  Definition normalized := true.
End Info.

Definition _BUF_MEM_grow : ident := $"BUF_MEM_grow".
Definition _CRYPTO_free : ident := $"CRYPTO_free".
Definition _CRYPTO_zalloc : ident := $"CRYPTO_zalloc".
Definition _WPACKET_allocate_bytes : ident := $"WPACKET_allocate_bytes".
Definition _WPACKET_cleanup : ident := $"WPACKET_cleanup".
Definition _WPACKET_get_curr : ident := $"WPACKET_get_curr".
Definition _WPACKET_init_static_len : ident := $"WPACKET_init_static_len".
Definition _WPACKET_memcpy : ident := $"WPACKET_memcpy".
Definition _WPACKET_put_bytes__ : ident := $"WPACKET_put_bytes__".
Definition _WPACKET_reserve_bytes : ident := $"WPACKET_reserve_bytes".
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
Definition ___stringlit_packet_1 : ident := $"__stringlit_packet_1".
Definition _allocbytes : ident := $"allocbytes".
Definition _buf : ident := $"buf".
Definition _buf_mem_st : ident := $"buf_mem_st".
Definition _curr : ident := $"curr".
Definition _data : ident := $"data".
Definition _dest : ident := $"dest".
Definition _endfirst : ident := $"endfirst".
Definition _flags : ident := $"flags".
Definition _len : ident := $"len".
Definition _lenbytes : ident := $"lenbytes".
Definition _lenchars : ident := $"lenchars".
Definition _length : ident := $"length".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _maxmaxsize : ident := $"maxmaxsize".
Definition _maxsize : ident := $"maxsize".
Definition _memcpy : ident := $"memcpy".
Definition _newlen : ident := $"newlen".
Definition _packet_len : ident := $"packet_len".
Definition _parent : ident := $"parent".
Definition _pkt : ident := $"pkt".
Definition _put_value : ident := $"put_value".
Definition _pwritten : ident := $"pwritten".
Definition _reflen : ident := $"reflen".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _staticbuf : ident := $"staticbuf".
Definition _sub : ident := $"sub".
Definition _subs : ident := $"subs".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _wpacket_intern_init_len : ident := $"wpacket_intern_init_len".
Definition _wpacket_st : ident := $"wpacket_st".
Definition _wpacket_sub : ident := $"wpacket_sub".
Definition _written : ident := $"written".
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

Definition v___stringlit_packet_1 := {|
  gvar_info := (tarray tschar 1);
  gvar_init := (Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_WPACKET_allocate_bytes := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_len, tulong) :: (_allocbytes, (tptr (tptr tuchar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _WPACKET_reserve_bytes (Tfunction
                                     ((tptr (Tstruct _wpacket_st noattr)) ::
                                      tulong :: (tptr (tptr tuchar)) :: nil)
                                     tint cc_default))
      ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) ::
       (Etempvar _len tulong) ::
       (Etempvar _allocbytes (tptr (tptr tuchar))) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _written tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _written tulong)
        (Ebinop Oadd (Etempvar _t'3 tulong) (Etempvar _len tulong) tulong)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _curr tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _curr tulong)
          (Ebinop Oadd (Etempvar _t'2 tulong) (Etempvar _len tulong) tulong)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_WPACKET_reserve_bytes := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_len, tulong) :: (_allocbytes, (tptr (tptr tuchar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_newlen, tulong) :: (_reflen, tulong) :: (_t'6, tint) ::
               (_t'5, (tptr tuchar)) :: (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tint) ::
               (_t'21, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_t'20, tulong) :: (_t'19, tulong) :: (_t'18, tulong) ::
               (_t'17, tulong) ::
               (_t'16, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'15, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'14, tulong) ::
               (_t'13, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'12, tulong) ::
               (_t'11, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'10, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'9, (tptr tuchar)) :: (_t'8, tuint) ::
               (_t'7, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'21
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _subs
          (tptr (Tstruct _wpacket_sub noattr))))
      (Sifthenelse (Ebinop One
                     (Etempvar _t'21 (tptr (Tstruct _wpacket_sub noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'1
          (Ecast
            (Ebinop One (Etempvar _len tulong) (Econst_int (Int.repr 0) tint)
              tint) tbool))
        (Sset _t'1 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Eunop Onotbool
                   (Ebinop One (Etempvar _t'1 tint)
                     (Econst_int (Int.repr 0) tint) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'19
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _maxsize tulong))
      (Ssequence
        (Sset _t'20
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _written tulong))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'19 tulong)
                         (Etempvar _t'20 tulong) tulong)
                       (Etempvar _len tulong) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                (Tstruct _wpacket_st noattr)) _buf
              (tptr (Tstruct _buf_mem_st noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'15 (tptr (Tstruct _buf_mem_st noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Sset _t'16
                (Efield
                  (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                    (Tstruct _wpacket_st noattr)) _buf
                  (tptr (Tstruct _buf_mem_st noattr))))
              (Ssequence
                (Sset _t'17
                  (Efield
                    (Ederef
                      (Etempvar _t'16 (tptr (Tstruct _buf_mem_st noattr)))
                      (Tstruct _buf_mem_st noattr)) _length tulong))
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef
                        (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                        (Tstruct _wpacket_st noattr)) _written tulong))
                  (Sset _t'4
                    (Ecast
                      (Ebinop Olt
                        (Ebinop Osub (Etempvar _t'17 tulong)
                          (Etempvar _t'18 tulong) tulong)
                        (Etempvar _len tulong) tint) tbool)))))
            (Sset _t'4 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'4 tint)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'11
                  (Efield
                    (Ederef
                      (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                      (Tstruct _wpacket_st noattr)) _buf
                    (tptr (Tstruct _buf_mem_st noattr))))
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef
                        (Etempvar _t'11 (tptr (Tstruct _buf_mem_st noattr)))
                        (Tstruct _buf_mem_st noattr)) _length tulong))
                  (Sifthenelse (Ebinop Ogt (Etempvar _len tulong)
                                 (Etempvar _t'12 tulong) tint)
                    (Sset _t'2 (Ecast (Etempvar _len tulong) tulong))
                    (Ssequence
                      (Sset _t'13
                        (Efield
                          (Ederef
                            (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                            (Tstruct _wpacket_st noattr)) _buf
                          (tptr (Tstruct _buf_mem_st noattr))))
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Ederef
                              (Etempvar _t'13 (tptr (Tstruct _buf_mem_st noattr)))
                              (Tstruct _buf_mem_st noattr)) _length tulong))
                        (Sset _t'2 (Ecast (Etempvar _t'14 tulong) tulong)))))))
              (Sset _reflen (Etempvar _t'2 tulong)))
            (Ssequence
              (Sifthenelse (Ebinop Ogt (Etempvar _reflen tulong)
                             (Ebinop Odiv
                               (Econst_long (Int64.repr (-1)) tulong)
                               (Econst_int (Int.repr 2) tint) tulong) tint)
                (Sset _newlen (Econst_long (Int64.repr (-1)) tulong))
                (Ssequence
                  (Sset _newlen
                    (Ebinop Omul (Etempvar _reflen tulong)
                      (Econst_int (Int.repr 2) tint) tulong))
                  (Sifthenelse (Ebinop Olt (Etempvar _newlen tulong)
                                 (Econst_int (Int.repr 256) tint) tint)
                    (Sset _newlen
                      (Ecast (Econst_int (Int.repr 256) tint) tulong))
                    Sskip)))
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef
                        (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                        (Tstruct _wpacket_st noattr)) _buf
                      (tptr (Tstruct _buf_mem_st noattr))))
                  (Scall (Some _t'3)
                    (Evar _BUF_MEM_grow (Tfunction
                                          ((tptr (Tstruct _buf_mem_st noattr)) ::
                                           tulong :: nil) tulong cc_default))
                    ((Etempvar _t'10 (tptr (Tstruct _buf_mem_st noattr))) ::
                     (Etempvar _newlen tulong) :: nil)))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tulong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))))
          Sskip))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _allocbytes (tptr (tptr tuchar)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _WPACKET_get_curr (Tfunction
                                          ((tptr (Tstruct _wpacket_st noattr)) ::
                                           nil) (tptr tuchar) cc_default))
                ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) :: nil))
              (Sassign
                (Ederef (Etempvar _allocbytes (tptr (tptr tuchar)))
                  (tptr tuchar)) (Etempvar _t'5 (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                      (Tstruct _wpacket_st noattr)) _endfirst tuint))
                (Sifthenelse (Etempvar _t'8 tuint)
                  (Ssequence
                    (Sset _t'9
                      (Ederef (Etempvar _allocbytes (tptr (tptr tuchar)))
                        (tptr tuchar)))
                    (Sset _t'6
                      (Ecast
                        (Ebinop One (Etempvar _t'9 (tptr tuchar))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                          tint) tbool)))
                  (Sset _t'6 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'6 tint)
                (Ssequence
                  (Sset _t'7
                    (Ederef (Etempvar _allocbytes (tptr (tptr tuchar)))
                      (tptr tuchar)))
                  (Sassign
                    (Ederef (Etempvar _allocbytes (tptr (tptr tuchar)))
                      (tptr tuchar))
                    (Ebinop Osub (Etempvar _t'7 (tptr tuchar))
                      (Etempvar _len tulong) (tptr tuchar))))
                Sskip)))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_maxmaxsize := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_lenbytes, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _lenbytes tulong)
                   (Esizeof tulong tulong) tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Sset _t'1
        (Ecast
          (Ebinop Oeq (Etempvar _lenbytes tulong)
            (Econst_int (Int.repr 0) tint) tint) tbool)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Econst_long (Int64.repr (-1)) tulong)))
      Sskip))
  (Sreturn (Some (Ebinop Oadd
                   (Ebinop Osub
                     (Ebinop Oshl
                       (Ecast (Econst_int (Int.repr 1) tint) tulong)
                       (Ebinop Omul (Etempvar _lenbytes tulong)
                         (Econst_int (Int.repr 8) tint) tulong) tulong)
                     (Econst_int (Int.repr 1) tint) tulong)
                   (Etempvar _lenbytes tulong) tulong))))
|}.

Definition f_wpacket_intern_init_len := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_lenbytes, tulong) :: nil);
  fn_vars := ((_lenchars, (tptr tuchar)) :: nil);
  fn_temps := ((_t'3, tint) ::
               (_t'2, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'7, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_t'6, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_t'5, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_t'4, (tptr (Tstruct _wpacket_sub noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
        (Tstruct _wpacket_st noattr)) _curr tulong)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
          (Tstruct _wpacket_st noattr)) _written tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _CRYPTO_zalloc (Tfunction
                                     (tulong :: (tptr tschar) :: tint :: nil)
                                     (tptr tvoid) cc_default))
              ((Esizeof (Tstruct _wpacket_sub noattr) tulong) ::
               (Evar ___stringlit_packet_1 (tarray tschar 1)) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sset _t'2
              (Ecast (Etempvar _t'1 (tptr tvoid))
                (tptr (Tstruct _wpacket_sub noattr)))))
          (Sassign
            (Efield
              (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                (Tstruct _wpacket_st noattr)) _subs
              (tptr (Tstruct _wpacket_sub noattr)))
            (Etempvar _t'2 (tptr (Tstruct _wpacket_sub noattr)))))
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _t'2 (tptr (Tstruct _wpacket_sub noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _lenbytes tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip)
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                  (Tstruct _wpacket_st noattr)) _subs
                (tptr (Tstruct _wpacket_sub noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _t'7 (tptr (Tstruct _wpacket_sub noattr)))
                  (Tstruct _wpacket_sub noattr)) _pwritten tulong)
              (Etempvar _lenbytes tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                    (Tstruct _wpacket_st noattr)) _subs
                  (tptr (Tstruct _wpacket_sub noattr))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _t'6 (tptr (Tstruct _wpacket_sub noattr)))
                    (Tstruct _wpacket_sub noattr)) _lenbytes tulong)
                (Etempvar _lenbytes tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _WPACKET_allocate_bytes (Tfunction
                                                  ((tptr (Tstruct _wpacket_st noattr)) ::
                                                   tulong ::
                                                   (tptr (tptr tuchar)) ::
                                                   nil) tint cc_default))
                  ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) ::
                   (Etempvar _lenbytes tulong) ::
                   (Eaddrof (Evar _lenchars (tptr tuchar))
                     (tptr (tptr tuchar))) :: nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef
                            (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                            (Tstruct _wpacket_st noattr)) _subs
                          (tptr (Tstruct _wpacket_sub noattr))))
                      (Scall None
                        (Evar _CRYPTO_free (Tfunction
                                             ((tptr tvoid) ::
                                              (tptr tschar) :: tint :: nil)
                                             tvoid cc_default))
                        ((Etempvar _t'5 (tptr (Tstruct _wpacket_sub noattr))) ::
                         (Evar ___stringlit_packet_1 (tarray tschar 1)) ::
                         (Econst_int (Int.repr 0) tint) :: nil)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                            (Tstruct _wpacket_st noattr)) _subs
                          (tptr (Tstruct _wpacket_sub noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                        (Tstruct _wpacket_st noattr)) _subs
                      (tptr (Tstruct _wpacket_sub noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _t'4 (tptr (Tstruct _wpacket_sub noattr)))
                        (Tstruct _wpacket_sub noattr)) _packet_len tulong)
                    (Econst_int (Int.repr 0) tint)))
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))
|}.

Definition f_WPACKET_init_static_len := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_buf, (tptr tuchar)) :: (_len, tulong) ::
                (_lenbytes, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_max, tulong) :: (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _maxmaxsize (Tfunction (tulong :: nil) tulong cc_default))
      ((Etempvar _lenbytes tulong) :: nil))
    (Sset _max (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _buf (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'2
          (Ecast
            (Ebinop Ogt (Etempvar _len tulong) (Econst_int (Int.repr 0) tint)
              tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Eunop Onotbool
                     (Ebinop One (Etempvar _t'2 tint)
                       (Econst_int (Int.repr 0) tint) tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _staticbuf (tptr tuchar))
        (Etempvar _buf (tptr tuchar)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _buf
            (tptr (Tstruct _buf_mem_st noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _max tulong)
                           (Etempvar _len tulong) tint)
              (Sset _t'3 (Ecast (Etempvar _max tulong) tulong))
              (Sset _t'3 (Ecast (Etempvar _len tulong) tulong)))
            (Sassign
              (Efield
                (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                  (Tstruct _wpacket_st noattr)) _maxsize tulong)
              (Etempvar _t'3 tulong)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                  (Tstruct _wpacket_st noattr)) _endfirst tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _wpacket_intern_init_len (Tfunction
                                                 ((tptr (Tstruct _wpacket_st noattr)) ::
                                                  tulong :: nil) tint
                                                 cc_default))
                ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) ::
                 (Etempvar _lenbytes tulong) :: nil))
              (Sreturn (Some (Etempvar _t'4 tint))))))))))
|}.

Definition f_put_value := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tuchar)) :: (_value, tulong) ::
                (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _data (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _data
        (Ebinop Oadd (Etempvar _data (tptr tuchar))
          (Ebinop Osub (Etempvar _len tulong) (Econst_int (Int.repr 1) tint)
            tulong) (tptr tuchar)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _len tulong)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign (Ederef (Etempvar _data (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oand (Etempvar _value tulong)
                  (Econst_int (Int.repr 255) tint) tulong) tuchar))
            (Ssequence
              (Sset _data
                (Ebinop Osub (Etempvar _data (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)))
              (Sset _value
                (Ebinop Oshr (Etempvar _value tulong)
                  (Econst_int (Int.repr 8) tint) tulong)))))
        (Sset _len
          (Ebinop Osub (Etempvar _len tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _value tulong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_WPACKET_put_bytes__ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_val, tulong) :: (_size, tulong) :: nil);
  fn_vars := ((_data, (tptr tuchar)) :: nil);
  fn_temps := ((_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'5, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Ebinop One
                       (Ebinop Ole (Etempvar _size tulong)
                         (Esizeof tulong tulong) tint)
                       (Econst_int (Int.repr 0) tint) tint) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Scall (Some _t'2)
            (Evar _WPACKET_allocate_bytes (Tfunction
                                            ((tptr (Tstruct _wpacket_st noattr)) ::
                                             tulong ::
                                             (tptr (tptr tuchar)) :: nil)
                                            tint cc_default))
            ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) ::
             (Etempvar _size tulong) ::
             (Eaddrof (Evar _data (tptr tuchar)) (tptr (tptr tuchar))) ::
             nil))
          (Sset _t'1
            (Ecast (Eunop Onotbool (Etempvar _t'2 tint) tint) tbool))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'3 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Ssequence
            (Sset _t'5 (Evar _data (tptr tuchar)))
            (Scall (Some _t'4)
              (Evar _put_value (Tfunction
                                 ((tptr tuchar) :: tulong :: tulong :: nil)
                                 tint cc_default))
              ((Etempvar _t'5 (tptr tuchar)) :: (Etempvar _val tulong) ::
               (Etempvar _size tulong) :: nil)))
          (Sset _t'3
            (Ecast (Eunop Onotbool (Etempvar _t'4 tint) tint) tbool)))))
    (Sifthenelse (Etempvar _t'3 tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_WPACKET_memcpy := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) ::
                (_src, (tptr tvoid)) :: (_len, tulong) :: nil);
  fn_vars := ((_dest, (tptr tuchar)) :: nil);
  fn_temps := ((_t'1, tint) :: (_t'3, (tptr tuchar)) ::
               (_t'2, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _len tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _WPACKET_allocate_bytes (Tfunction
                                        ((tptr (Tstruct _wpacket_st noattr)) ::
                                         tulong :: (tptr (tptr tuchar)) ::
                                         nil) tint cc_default))
        ((Etempvar _pkt (tptr (Tstruct _wpacket_st noattr))) ::
         (Etempvar _len tulong) ::
         (Eaddrof (Evar _dest (tptr tuchar)) (tptr (tptr tuchar))) :: nil))
      (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'2 (Evar _dest (tptr tuchar)))
        (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr tuchar))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _t'3 (Evar _dest (tptr tuchar)))
            (Scall None
              (Evar _memcpy (Tfunction
                              ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                              (tptr tvoid) cc_default))
              ((Etempvar _t'3 (tptr tuchar)) ::
               (Etempvar _src (tptr tvoid)) :: (Etempvar _len tulong) :: nil)))
          Sskip))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_WPACKET_get_curr := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_buf, (tptr tuchar)) :: (_t'1, (tptr tvoid)) ::
               (_t'10, (tptr tuchar)) :: (_t'9, (tptr tschar)) ::
               (_t'8, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'7, (tptr (Tstruct _buf_mem_st noattr))) ::
               (_t'6, (tptr tuchar)) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tuint) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
            (Tstruct _wpacket_st noattr)) _staticbuf (tptr tuchar)))
      (Sifthenelse (Ebinop One (Etempvar _t'6 (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                (Tstruct _wpacket_st noattr)) _staticbuf (tptr tuchar)))
          (Sset _t'1 (Ecast (Etempvar _t'10 (tptr tuchar)) (tptr tvoid))))
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                (Tstruct _wpacket_st noattr)) _buf
              (tptr (Tstruct _buf_mem_st noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'7 (tptr (Tstruct _buf_mem_st noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                      (Tstruct _wpacket_st noattr)) _buf
                    (tptr (Tstruct _buf_mem_st noattr))))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _t'8 (tptr (Tstruct _buf_mem_st noattr)))
                        (Tstruct _buf_mem_st noattr)) _data (tptr tschar)))
                  (Sset _t'1
                    (Ecast
                      (Ecast (Etempvar _t'9 (tptr tschar)) (tptr tuchar))
                      (tptr tvoid)))))
              (Sset _t'1 (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tvoid))))
            (Ssequence
              (Sset _t'1
                (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                  (tptr tvoid)))
              (Sset _t'1 (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tvoid))))))))
    (Sset _buf (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _buf (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _endfirst tuint))
        (Sifthenelse (Etempvar _t'3 tuint)
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                  (Tstruct _wpacket_st noattr)) _maxsize tulong))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
                    (Tstruct _wpacket_st noattr)) _curr tulong))
              (Sreturn (Some (Ebinop Osub
                               (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                                 (Etempvar _t'4 tulong) (tptr tuchar))
                               (Etempvar _t'5 tulong) (tptr tuchar))))))
          Sskip))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
              (Tstruct _wpacket_st noattr)) _curr tulong))
        (Sreturn (Some (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                         (Etempvar _t'2 tulong) (tptr tuchar))))))))
|}.

Definition f_WPACKET_cleanup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pkt, (tptr (Tstruct _wpacket_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_sub, (tptr (Tstruct _wpacket_sub noattr))) ::
               (_parent, (tptr (Tstruct _wpacket_sub noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _sub
      (Efield
        (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
          (Tstruct _wpacket_st noattr)) _subs
        (tptr (Tstruct _wpacket_sub noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop One
                       (Etempvar _sub (tptr (Tstruct _wpacket_sub noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _parent
            (Efield
              (Ederef (Etempvar _sub (tptr (Tstruct _wpacket_sub noattr)))
                (Tstruct _wpacket_sub noattr)) _parent
              (tptr (Tstruct _wpacket_sub noattr))))
          (Scall None
            (Evar _CRYPTO_free (Tfunction
                                 ((tptr tvoid) :: (tptr tschar) :: tint ::
                                  nil) tvoid cc_default))
            ((Etempvar _sub (tptr (Tstruct _wpacket_sub noattr))) ::
             (Evar ___stringlit_packet_1 (tarray tschar 1)) ::
             (Econst_int (Int.repr 0) tint) :: nil))))
      (Sset _sub (Etempvar _parent (tptr (Tstruct _wpacket_sub noattr))))))
  (Sassign
    (Efield
      (Ederef (Etempvar _pkt (tptr (Tstruct _wpacket_st noattr)))
        (Tstruct _wpacket_st noattr)) _subs
      (tptr (Tstruct _wpacket_sub noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
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
     cc_default)) :: (___stringlit_packet_1, Gvar v___stringlit_packet_1) ::
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
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_CRYPTO_zalloc,
   Gfun(External (EF_external "CRYPTO_zalloc"
                   (mksignature (AST.Xlong :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xptr cc_default))
     (tulong :: (tptr tschar) :: tint :: nil) (tptr tvoid) cc_default)) ::
 (_CRYPTO_free,
   Gfun(External (EF_external "CRYPTO_free"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tschar) :: tint :: nil) tvoid cc_default)) ::
 (_BUF_MEM_grow,
   Gfun(External (EF_external "BUF_MEM_grow"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xlong
                     cc_default))
     ((tptr (Tstruct _buf_mem_st noattr)) :: tulong :: nil) tulong
     cc_default)) ::
 (_WPACKET_allocate_bytes, Gfun(Internal f_WPACKET_allocate_bytes)) ::
 (_WPACKET_reserve_bytes, Gfun(Internal f_WPACKET_reserve_bytes)) ::
 (_maxmaxsize, Gfun(Internal f_maxmaxsize)) ::
 (_wpacket_intern_init_len, Gfun(Internal f_wpacket_intern_init_len)) ::
 (_WPACKET_init_static_len, Gfun(Internal f_WPACKET_init_static_len)) ::
 (_put_value, Gfun(Internal f_put_value)) ::
 (_WPACKET_put_bytes__, Gfun(Internal f_WPACKET_put_bytes__)) ::
 (_WPACKET_memcpy, Gfun(Internal f_WPACKET_memcpy)) ::
 (_WPACKET_get_curr, Gfun(Internal f_WPACKET_get_curr)) ::
 (_WPACKET_cleanup, Gfun(Internal f_WPACKET_cleanup)) :: nil).

Definition public_idents : list ident :=
(_WPACKET_cleanup :: _WPACKET_get_curr :: _WPACKET_memcpy ::
 _WPACKET_put_bytes__ :: _WPACKET_init_static_len ::
 _WPACKET_reserve_bytes :: _WPACKET_allocate_bytes :: _BUF_MEM_grow ::
 _CRYPTO_free :: _CRYPTO_zalloc :: _memcpy :: ___builtin_debug ::
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


