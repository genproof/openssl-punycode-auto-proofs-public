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
  Definition source_file := "harness/rfc_samples.c".
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
Definition ___stringlit_rfc_samples_1 : ident := $"__stringlit_rfc_samples_1".
Definition ___stringlit_rfc_samples_10 : ident := $"__stringlit_rfc_samples_10".
Definition ___stringlit_rfc_samples_11 : ident := $"__stringlit_rfc_samples_11".
Definition ___stringlit_rfc_samples_12 : ident := $"__stringlit_rfc_samples_12".
Definition ___stringlit_rfc_samples_13 : ident := $"__stringlit_rfc_samples_13".
Definition ___stringlit_rfc_samples_14 : ident := $"__stringlit_rfc_samples_14".
Definition ___stringlit_rfc_samples_15 : ident := $"__stringlit_rfc_samples_15".
Definition ___stringlit_rfc_samples_16 : ident := $"__stringlit_rfc_samples_16".
Definition ___stringlit_rfc_samples_17 : ident := $"__stringlit_rfc_samples_17".
Definition ___stringlit_rfc_samples_18 : ident := $"__stringlit_rfc_samples_18".
Definition ___stringlit_rfc_samples_19 : ident := $"__stringlit_rfc_samples_19".
Definition ___stringlit_rfc_samples_2 : ident := $"__stringlit_rfc_samples_2".
Definition ___stringlit_rfc_samples_3 : ident := $"__stringlit_rfc_samples_3".
Definition ___stringlit_rfc_samples_4 : ident := $"__stringlit_rfc_samples_4".
Definition ___stringlit_rfc_samples_5 : ident := $"__stringlit_rfc_samples_5".
Definition ___stringlit_rfc_samples_6 : ident := $"__stringlit_rfc_samples_6".
Definition ___stringlit_rfc_samples_7 : ident := $"__stringlit_rfc_samples_7".
Definition ___stringlit_rfc_samples_8 : ident := $"__stringlit_rfc_samples_8".
Definition ___stringlit_rfc_samples_9 : ident := $"__stringlit_rfc_samples_9".
Definition _a : ident := $"a".
Definition _any_uints : ident := $"any_uints".
Definition _at : ident := $"at".
Definition _b : ident := $"b".
Definition _count : ident := $"count".
Definition _decoded : ident := $"decoded".
Definition _encoded : ident := $"encoded".
Definition _gp_assert : ident := $"gp_assert".
Definition _i : ident := $"i".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _ossl_punycode_decode : ident := $"ossl_punycode_decode".
Definition _out : ident := $"out".
Definition _points : ident := $"points".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _s : ident := $"s".
Definition _uints_eq : ident := $"uints_eq".
Definition _values : ident := $"values".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_rfc_samples_8 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_2 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_4 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 75) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_17 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_19 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_3 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_18 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_13 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_6 := {|
  gvar_info := (tarray tschar 41);
  gvar_init := (Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_1 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 36) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_5 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_9 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_12 := {|
  gvar_info := (tarray tschar 70);
  gvar_init := (Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_15 := {|
  gvar_info := (tarray tschar 29);
  gvar_init := (Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_11 := {|
  gvar_info := (tarray tschar 33);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_16 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_10 := {|
  gvar_info := (tarray tschar 46);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_14 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 106) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_rfc_samples_7 := {|
  gvar_info := (tarray tschar 41);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 89) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
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

Definition v_encoded := {|
  gvar_info := (tarray (tptr tschar) 19);
  gvar_init := (Init_addrof ___stringlit_rfc_samples_19 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_18 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_17 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_16 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_15 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_14 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_13 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_12 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_11 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_10 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_9 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_8 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_7 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_6 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_5 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_4 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_3 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_2 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_rfc_samples_1 (Ptrofs.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_points := {|
  gvar_info := (tarray tuchar 19);
  gvar_init := (Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 30) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 31) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 11) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_decoded := {|
  gvar_info := (tarray tuint 355);
  gvar_init := (Init_int32 (Int.repr 1604) :: Init_int32 (Int.repr 1610) ::
                Init_int32 (Int.repr 1607) :: Init_int32 (Int.repr 1605) ::
                Init_int32 (Int.repr 1575) :: Init_int32 (Int.repr 1576) ::
                Init_int32 (Int.repr 1578) :: Init_int32 (Int.repr 1603) ::
                Init_int32 (Int.repr 1604) :: Init_int32 (Int.repr 1605) ::
                Init_int32 (Int.repr 1608) :: Init_int32 (Int.repr 1588) ::
                Init_int32 (Int.repr 1593) :: Init_int32 (Int.repr 1585) ::
                Init_int32 (Int.repr 1576) :: Init_int32 (Int.repr 1610) ::
                Init_int32 (Int.repr 1567) :: Init_int32 (Int.repr 20182) ::
                Init_int32 (Int.repr 20204) :: Init_int32 (Int.repr 20026) ::
                Init_int32 (Int.repr 20160) :: Init_int32 (Int.repr 20040) ::
                Init_int32 (Int.repr 19981) :: Init_int32 (Int.repr 35828) ::
                Init_int32 (Int.repr 20013) :: Init_int32 (Int.repr 25991) ::
                Init_int32 (Int.repr 20182) :: Init_int32 (Int.repr 20497) ::
                Init_int32 (Int.repr 29234) :: Init_int32 (Int.repr 20160) ::
                Init_int32 (Int.repr 40637) :: Init_int32 (Int.repr 19981) ::
                Init_int32 (Int.repr 35498) :: Init_int32 (Int.repr 20013) ::
                Init_int32 (Int.repr 25991) :: Init_int32 (Int.repr 80) ::
                Init_int32 (Int.repr 114) :: Init_int32 (Int.repr 111) ::
                Init_int32 (Int.repr 269) :: Init_int32 (Int.repr 112) ::
                Init_int32 (Int.repr 114) :: Init_int32 (Int.repr 111) ::
                Init_int32 (Int.repr 115) :: Init_int32 (Int.repr 116) ::
                Init_int32 (Int.repr 283) :: Init_int32 (Int.repr 110) ::
                Init_int32 (Int.repr 101) :: Init_int32 (Int.repr 109) ::
                Init_int32 (Int.repr 108) :: Init_int32 (Int.repr 117) ::
                Init_int32 (Int.repr 118) :: Init_int32 (Int.repr 237) ::
                Init_int32 (Int.repr 269) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 115) :: Init_int32 (Int.repr 107) ::
                Init_int32 (Int.repr 121) :: Init_int32 (Int.repr 1500) ::
                Init_int32 (Int.repr 1502) :: Init_int32 (Int.repr 1492) ::
                Init_int32 (Int.repr 1492) :: Init_int32 (Int.repr 1501) ::
                Init_int32 (Int.repr 1508) :: Init_int32 (Int.repr 1513) ::
                Init_int32 (Int.repr 1493) :: Init_int32 (Int.repr 1496) ::
                Init_int32 (Int.repr 1500) :: Init_int32 (Int.repr 1488) ::
                Init_int32 (Int.repr 1502) :: Init_int32 (Int.repr 1491) ::
                Init_int32 (Int.repr 1489) :: Init_int32 (Int.repr 1512) ::
                Init_int32 (Int.repr 1497) :: Init_int32 (Int.repr 1501) ::
                Init_int32 (Int.repr 1506) :: Init_int32 (Int.repr 1489) ::
                Init_int32 (Int.repr 1512) :: Init_int32 (Int.repr 1497) ::
                Init_int32 (Int.repr 1514) :: Init_int32 (Int.repr 2351) ::
                Init_int32 (Int.repr 2361) :: Init_int32 (Int.repr 2354) ::
                Init_int32 (Int.repr 2379) :: Init_int32 (Int.repr 2327) ::
                Init_int32 (Int.repr 2361) :: Init_int32 (Int.repr 2367) ::
                Init_int32 (Int.repr 2344) :: Init_int32 (Int.repr 2381) ::
                Init_int32 (Int.repr 2342) :: Init_int32 (Int.repr 2368) ::
                Init_int32 (Int.repr 2325) :: Init_int32 (Int.repr 2381) ::
                Init_int32 (Int.repr 2351) :: Init_int32 (Int.repr 2379) ::
                Init_int32 (Int.repr 2306) :: Init_int32 (Int.repr 2344) ::
                Init_int32 (Int.repr 2361) :: Init_int32 (Int.repr 2368) ::
                Init_int32 (Int.repr 2306) :: Init_int32 (Int.repr 2348) ::
                Init_int32 (Int.repr 2379) :: Init_int32 (Int.repr 2354) ::
                Init_int32 (Int.repr 2360) :: Init_int32 (Int.repr 2325) ::
                Init_int32 (Int.repr 2340) :: Init_int32 (Int.repr 2375) ::
                Init_int32 (Int.repr 2361) :: Init_int32 (Int.repr 2376) ::
                Init_int32 (Int.repr 2306) :: Init_int32 (Int.repr 12394) ::
                Init_int32 (Int.repr 12380) :: Init_int32 (Int.repr 12415) ::
                Init_int32 (Int.repr 12435) :: Init_int32 (Int.repr 12394) ::
                Init_int32 (Int.repr 26085) :: Init_int32 (Int.repr 26412) ::
                Init_int32 (Int.repr 35486) :: Init_int32 (Int.repr 12434) ::
                Init_int32 (Int.repr 35441) :: Init_int32 (Int.repr 12375) ::
                Init_int32 (Int.repr 12390) :: Init_int32 (Int.repr 12367) ::
                Init_int32 (Int.repr 12428) :: Init_int32 (Int.repr 12394) ::
                Init_int32 (Int.repr 12356) :: Init_int32 (Int.repr 12398) ::
                Init_int32 (Int.repr 12363) :: Init_int32 (Int.repr 49464) ::
                Init_int32 (Int.repr 44228) :: Init_int32 (Int.repr 51032) ::
                Init_int32 (Int.repr 47784) :: Init_int32 (Int.repr 46304) ::
                Init_int32 (Int.repr 49324) :: Init_int32 (Int.repr 46988) ::
                Init_int32 (Int.repr 46308) :: Init_int32 (Int.repr 51060) ::
                Init_int32 (Int.repr 54620) :: Init_int32 (Int.repr 44397) ::
                Init_int32 (Int.repr 50612) :: Init_int32 (Int.repr 47484) ::
                Init_int32 (Int.repr 51060) :: Init_int32 (Int.repr 54644) ::
                Init_int32 (Int.repr 54620) :: Init_int32 (Int.repr 45796) ::
                Init_int32 (Int.repr 47732) :: Init_int32 (Int.repr 50620) ::
                Init_int32 (Int.repr 47560) :: Init_int32 (Int.repr 45208) ::
                Init_int32 (Int.repr 51339) :: Init_int32 (Int.repr 51012) ::
                Init_int32 (Int.repr 44620) :: Init_int32 (Int.repr 1087) ::
                Init_int32 (Int.repr 1086) :: Init_int32 (Int.repr 1095) ::
                Init_int32 (Int.repr 1077) :: Init_int32 (Int.repr 1084) ::
                Init_int32 (Int.repr 1091) :: Init_int32 (Int.repr 1078) ::
                Init_int32 (Int.repr 1077) :: Init_int32 (Int.repr 1086) ::
                Init_int32 (Int.repr 1085) :: Init_int32 (Int.repr 1080) ::
                Init_int32 (Int.repr 1085) :: Init_int32 (Int.repr 1077) ::
                Init_int32 (Int.repr 1075) :: Init_int32 (Int.repr 1086) ::
                Init_int32 (Int.repr 1074) :: Init_int32 (Int.repr 1086) ::
                Init_int32 (Int.repr 1088) :: Init_int32 (Int.repr 1103) ::
                Init_int32 (Int.repr 1090) :: Init_int32 (Int.repr 1087) ::
                Init_int32 (Int.repr 1086) :: Init_int32 (Int.repr 1088) ::
                Init_int32 (Int.repr 1091) :: Init_int32 (Int.repr 1089) ::
                Init_int32 (Int.repr 1089) :: Init_int32 (Int.repr 1082) ::
                Init_int32 (Int.repr 1080) :: Init_int32 (Int.repr 80) ::
                Init_int32 (Int.repr 111) :: Init_int32 (Int.repr 114) ::
                Init_int32 (Int.repr 113) :: Init_int32 (Int.repr 117) ::
                Init_int32 (Int.repr 233) :: Init_int32 (Int.repr 110) ::
                Init_int32 (Int.repr 111) :: Init_int32 (Int.repr 112) ::
                Init_int32 (Int.repr 117) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 100) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 110) :: Init_int32 (Int.repr 115) ::
                Init_int32 (Int.repr 105) :: Init_int32 (Int.repr 109) ::
                Init_int32 (Int.repr 112) :: Init_int32 (Int.repr 108) ::
                Init_int32 (Int.repr 101) :: Init_int32 (Int.repr 109) ::
                Init_int32 (Int.repr 101) :: Init_int32 (Int.repr 110) ::
                Init_int32 (Int.repr 116) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 104) :: Init_int32 (Int.repr 97) ::
                Init_int32 (Int.repr 98) :: Init_int32 (Int.repr 108) ::
                Init_int32 (Int.repr 97) :: Init_int32 (Int.repr 114) ::
                Init_int32 (Int.repr 101) :: Init_int32 (Int.repr 110) ::
                Init_int32 (Int.repr 69) :: Init_int32 (Int.repr 115) ::
                Init_int32 (Int.repr 112) :: Init_int32 (Int.repr 97) ::
                Init_int32 (Int.repr 241) :: Init_int32 (Int.repr 111) ::
                Init_int32 (Int.repr 108) :: Init_int32 (Int.repr 84) ::
                Init_int32 (Int.repr 7841) :: Init_int32 (Int.repr 105) ::
                Init_int32 (Int.repr 115) :: Init_int32 (Int.repr 97) ::
                Init_int32 (Int.repr 111) :: Init_int32 (Int.repr 104) ::
                Init_int32 (Int.repr 7885) :: Init_int32 (Int.repr 107) ::
                Init_int32 (Int.repr 104) :: Init_int32 (Int.repr 244) ::
                Init_int32 (Int.repr 110) :: Init_int32 (Int.repr 103) ::
                Init_int32 (Int.repr 116) :: Init_int32 (Int.repr 104) ::
                Init_int32 (Int.repr 7875) :: Init_int32 (Int.repr 99) ::
                Init_int32 (Int.repr 104) :: Init_int32 (Int.repr 7881) ::
                Init_int32 (Int.repr 110) :: Init_int32 (Int.repr 243) ::
                Init_int32 (Int.repr 105) :: Init_int32 (Int.repr 116) ::
                Init_int32 (Int.repr 105) :: Init_int32 (Int.repr 7871) ::
                Init_int32 (Int.repr 110) :: Init_int32 (Int.repr 103) ::
                Init_int32 (Int.repr 86) :: Init_int32 (Int.repr 105) ::
                Init_int32 (Int.repr 7879) :: Init_int32 (Int.repr 116) ::
                Init_int32 (Int.repr 51) :: Init_int32 (Int.repr 24180) ::
                Init_int32 (Int.repr 66) :: Init_int32 (Int.repr 32068) ::
                Init_int32 (Int.repr 37329) :: Init_int32 (Int.repr 20843) ::
                Init_int32 (Int.repr 20808) :: Init_int32 (Int.repr 29983) ::
                Init_int32 (Int.repr 23433) :: Init_int32 (Int.repr 23460) ::
                Init_int32 (Int.repr 22856) :: Init_int32 (Int.repr 32654) ::
                Init_int32 (Int.repr 24693) :: Init_int32 (Int.repr 45) ::
                Init_int32 (Int.repr 119) :: Init_int32 (Int.repr 105) ::
                Init_int32 (Int.repr 116) :: Init_int32 (Int.repr 104) ::
                Init_int32 (Int.repr 45) :: Init_int32 (Int.repr 83) ::
                Init_int32 (Int.repr 85) :: Init_int32 (Int.repr 80) ::
                Init_int32 (Int.repr 69) :: Init_int32 (Int.repr 82) ::
                Init_int32 (Int.repr 45) :: Init_int32 (Int.repr 77) ::
                Init_int32 (Int.repr 79) :: Init_int32 (Int.repr 78) ::
                Init_int32 (Int.repr 75) :: Init_int32 (Int.repr 69) ::
                Init_int32 (Int.repr 89) :: Init_int32 (Int.repr 83) ::
                Init_int32 (Int.repr 72) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 108) :: Init_int32 (Int.repr 108) ::
                Init_int32 (Int.repr 111) :: Init_int32 (Int.repr 45) ::
                Init_int32 (Int.repr 65) :: Init_int32 (Int.repr 110) ::
                Init_int32 (Int.repr 111) :: Init_int32 (Int.repr 116) ::
                Init_int32 (Int.repr 104) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 114) :: Init_int32 (Int.repr 45) ::
                Init_int32 (Int.repr 87) :: Init_int32 (Int.repr 97) ::
                Init_int32 (Int.repr 121) :: Init_int32 (Int.repr 45) ::
                Init_int32 (Int.repr 12381) :: Init_int32 (Int.repr 12428) ::
                Init_int32 (Int.repr 12382) :: Init_int32 (Int.repr 12428) ::
                Init_int32 (Int.repr 12398) :: Init_int32 (Int.repr 22580) ::
                Init_int32 (Int.repr 25152) :: Init_int32 (Int.repr 12402) ::
                Init_int32 (Int.repr 12392) :: Init_int32 (Int.repr 12388) ::
                Init_int32 (Int.repr 23627) :: Init_int32 (Int.repr 26681) ::
                Init_int32 (Int.repr 12398) :: Init_int32 (Int.repr 19979) ::
                Init_int32 (Int.repr 50) :: Init_int32 (Int.repr 77) ::
                Init_int32 (Int.repr 97) :: Init_int32 (Int.repr 106) ::
                Init_int32 (Int.repr 105) :: Init_int32 (Int.repr 12391) ::
                Init_int32 (Int.repr 75) :: Init_int32 (Int.repr 111) ::
                Init_int32 (Int.repr 105) :: Init_int32 (Int.repr 12377) ::
                Init_int32 (Int.repr 12427) :: Init_int32 (Int.repr 53) ::
                Init_int32 (Int.repr 31186) :: Init_int32 (Int.repr 21069) ::
                Init_int32 (Int.repr 12497) :: Init_int32 (Int.repr 12501) ::
                Init_int32 (Int.repr 12451) :: Init_int32 (Int.repr 12540) ::
                Init_int32 (Int.repr 100) :: Init_int32 (Int.repr 101) ::
                Init_int32 (Int.repr 12523) :: Init_int32 (Int.repr 12531) ::
                Init_int32 (Int.repr 12496) :: Init_int32 (Int.repr 12381) ::
                Init_int32 (Int.repr 12398) :: Init_int32 (Int.repr 12473) ::
                Init_int32 (Int.repr 12500) :: Init_int32 (Int.repr 12540) ::
                Init_int32 (Int.repr 12489) :: Init_int32 (Int.repr 12391) ::
                Init_int32 (Int.repr 45) :: Init_int32 (Int.repr 62) ::
                Init_int32 (Int.repr 32) :: Init_int32 (Int.repr 36) ::
                Init_int32 (Int.repr 49) :: Init_int32 (Int.repr 46) ::
                Init_int32 (Int.repr 48) :: Init_int32 (Int.repr 48) ::
                Init_int32 (Int.repr 32) :: Init_int32 (Int.repr 60) ::
                Init_int32 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_count, tuint) :: nil);
  fn_temps := ((_at, tulong) :: (_s, tint) :: (_len, tulong) ::
               (_out, (tptr tuint)) :: (_r, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr tuint)) :: (_t'14, tschar) ::
               (_t'13, (tptr tschar)) :: (_t'12, tuchar) ::
               (_t'11, tuchar) :: (_t'10, (tptr tschar)) :: (_t'9, tuchar) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _at (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Ssequence
        (Sset _s (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _s tint)
                           (Econst_int (Int.repr 19) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _len (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'13
                        (Ederef
                          (Ebinop Oadd
                            (Evar _encoded (tarray (tptr tschar) 19))
                            (Etempvar _s tint) (tptr (tptr tschar)))
                          (tptr tschar)))
                      (Ssequence
                        (Sset _t'14
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'13 (tptr tschar))
                              (Etempvar _len tulong) (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop One (Etempvar _t'14 tschar)
                                       (Econst_int (Int.repr 0) tint) tint)
                          Sskip
                          Sbreak)))
                    (Sset _len
                      (Ebinop Oadd (Etempvar _len tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'12
                        (Ederef
                          (Ebinop Oadd (Evar _points (tarray tuchar 19))
                            (Etempvar _s tint) (tptr tuchar)) tuchar))
                      (Scall (Some _t'1)
                        (Evar _any_uints (Tfunction (tulong :: nil)
                                           (tptr tuint) cc_default))
                        ((Etempvar _t'12 tuchar) :: nil)))
                    (Sset _out (Etempvar _t'1 (tptr tuint))))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _out (tptr tuint))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                      Sskip)
                    (Ssequence
                      (Ssequence
                        (Sset _t'11
                          (Ederef
                            (Ebinop Oadd (Evar _points (tarray tuchar 19))
                              (Etempvar _s tint) (tptr tuchar)) tuchar))
                        (Sassign (Evar _count tuint) (Etempvar _t'11 tuchar)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'10
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _encoded (tarray (tptr tschar) 19))
                                  (Etempvar _s tint) (tptr (tptr tschar)))
                                (tptr tschar)))
                            (Scall (Some _t'2)
                              (Evar _ossl_punycode_decode (Tfunction
                                                            ((tptr tschar) ::
                                                             tulong ::
                                                             (tptr tuint) ::
                                                             (tptr tuint) ::
                                                             nil) tint
                                                            cc_default))
                              ((Etempvar _t'10 (tptr tschar)) ::
                               (Etempvar _len tulong) ::
                               (Etempvar _out (tptr tuint)) ::
                               (Eaddrof (Evar _count tuint) (tptr tuint)) ::
                               nil)))
                          (Sset _r (Etempvar _t'2 tint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint)
                                (Ssequence
                                  (Sset _t'8 (Evar _count tuint))
                                  (Ssequence
                                    (Sset _t'9
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _points (tarray tuchar 19))
                                          (Etempvar _s tint) (tptr tuchar))
                                        tuchar))
                                    (Sset _t'3
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'8 tuint)
                                          (Etempvar _t'9 tuchar) tint) tbool))))
                                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'3 tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'7 (Evar _count tuint))
                                    (Scall (Some _t'5)
                                      (Evar _uints_eq (Tfunction
                                                        ((tptr tuint) ::
                                                         (tptr tuint) ::
                                                         tulong :: nil) tint
                                                        cc_default))
                                      ((Etempvar _out (tptr tuint)) ::
                                       (Ebinop Oadd
                                         (Evar _decoded (tarray tuint 355))
                                         (Etempvar _at tulong) (tptr tuint)) ::
                                       (Etempvar _t'7 tuint) :: nil)))
                                  (Sset _t'4
                                    (Ecast (Etempvar _t'5 tint) tbool)))
                                (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Etempvar _t'4 tint) :: nil)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'6
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _points (tarray tuchar 19))
                                    (Etempvar _s tint) (tptr tuchar)) tuchar))
                              (Sset _at
                                (Ebinop Oadd (Etempvar _at tulong)
                                  (Etempvar _t'6 tuchar) tulong)))
                            (Scall None
                              (Evar _quickproof_free (Tfunction
                                                       ((tptr tvoid) :: nil)
                                                       tvoid cc_default))
                              ((Etempvar _out (tptr tuint)) :: nil)))))))))))
          (Sset _s
            (Ebinop Oadd (Etempvar _s tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
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
     cc_default)) :: (___stringlit_rfc_samples_8, Gvar v___stringlit_rfc_samples_8) ::
 (___stringlit_rfc_samples_2, Gvar v___stringlit_rfc_samples_2) ::
 (___stringlit_rfc_samples_4, Gvar v___stringlit_rfc_samples_4) ::
 (___stringlit_rfc_samples_17, Gvar v___stringlit_rfc_samples_17) ::
 (___stringlit_rfc_samples_19, Gvar v___stringlit_rfc_samples_19) ::
 (___stringlit_rfc_samples_3, Gvar v___stringlit_rfc_samples_3) ::
 (___stringlit_rfc_samples_18, Gvar v___stringlit_rfc_samples_18) ::
 (___stringlit_rfc_samples_13, Gvar v___stringlit_rfc_samples_13) ::
 (___stringlit_rfc_samples_6, Gvar v___stringlit_rfc_samples_6) ::
 (___stringlit_rfc_samples_1, Gvar v___stringlit_rfc_samples_1) ::
 (___stringlit_rfc_samples_5, Gvar v___stringlit_rfc_samples_5) ::
 (___stringlit_rfc_samples_9, Gvar v___stringlit_rfc_samples_9) ::
 (___stringlit_rfc_samples_12, Gvar v___stringlit_rfc_samples_12) ::
 (___stringlit_rfc_samples_15, Gvar v___stringlit_rfc_samples_15) ::
 (___stringlit_rfc_samples_11, Gvar v___stringlit_rfc_samples_11) ::
 (___stringlit_rfc_samples_16, Gvar v___stringlit_rfc_samples_16) ::
 (___stringlit_rfc_samples_10, Gvar v___stringlit_rfc_samples_10) ::
 (___stringlit_rfc_samples_14, Gvar v___stringlit_rfc_samples_14) ::
 (___stringlit_rfc_samples_7, Gvar v___stringlit_rfc_samples_7) ::
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
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
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
     cc_default)) :: (_any_uints, Gfun(Internal f_any_uints)) ::
 (_uints_eq, Gfun(Internal f_uints_eq)) :: (_encoded, Gvar v_encoded) ::
 (_points, Gvar v_points) :: (_decoded, Gvar v_decoded) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _ossl_punycode_decode :: _gp_assert :: _nondet_u32 ::
 _quickproof_free :: _quickproof_malloc :: ___builtin_debug ::
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


