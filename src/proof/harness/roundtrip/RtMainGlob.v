(* Lemmas for the start of the main of harness/x_roundtrip.c: the globals main keeps, mem_mgr, what malloc returned.
  *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.punycode.code OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib.
Local Open Scope logic.

Module PC := OpensslPunycode.punycode.code.
Module SC := OpensslPunycode.shim.code.

(* The globals of the law's program that main hands to ossl_punycode_decode / ossl_a2ulabel. *)
Lemma main_globals (gv: globals):
  data_at Ers tuint (Vint (Int.repr 36)) (gv PC._base) * data_at Ers tuint (Vint (Int.repr 26)) (gv PC._tmax) *
  data_at Ers tuint (Vint (Int.repr 1)) (gv PC._tmin) *
  data_at Ers tuchar (Vint (Int.zero_ext 8 (Int.repr 45))) (gv PC._delimiter) *
  data_at Ers tuint (Vint (Int.repr 700)) (gv PC._damp) *
  data_at Ers (tarray tschar 5) (map (Vint oo cast_int_int I8 Signed)
     [Int.repr 120; Int.repr 110; Int.repr 45; Int.repr 45; Int.repr 0]) (gv PC.___stringlit_punycode_1) *
  data_at Ers tuint (Vint (Int.repr (-1))) (gv PC._maxint) *
  data_at Ers tuint (Vint (Int.repr 128)) (gv PC._initial_n) *
  data_at Ers tuint (Vint (Int.repr 72)) (gv PC._initial_bias) *
  data_at Ers tuint (Vint (Int.repr 38)) (gv PC._skew) *
  data_at Ews tint (zero_val tint) (gv SC._ossl_shim_fail_next) *
  data_at Ews tint (zero_val tint) (gv SC._ossl_shim_zalloc_failed) *
  data_at Ews (Tlong Signed noattr) (zero_val (Tlong Signed noattr)) (gv SC._ossl_shim_live)
  |-- OpensslPunycode.proof.punycode.PunySpec.puny_consts gv * OpensslPunycode.proof.punycode.PunySpec.xn_lit gv *
      OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0.
Proof.
  unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts, OpensslPunycode.proof.punycode.PunySpec.xn_lit,
    OpensslPunycode.proof.shim.ShimSpec.shim_state.
  change (@data_at OpensslPunycode.proof.punycode.PunySpec.CS) with (@data_at CS).
  rewrite !(data_at_cs_tint OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite (data_at_cs_tlong OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite <- (data_at_tuchar_tschar_1 Ers 45) by lia.
  change (Int.zero_ext 8 (Int.repr 45)) with (Int.repr 45).
  change (map (Vint oo cast_int_int I8 Signed) [Int.repr 120; Int.repr 110; Int.repr 45; Int.repr 45; Int.repr 0])
    with (vb [120; 110; 45; 45; 0]).
  rewrite !zero_val_tint. change (Tlong Signed noattr) with tlong. rewrite zero_val_tlong.
  cancel.
Qed.

Lemma add_mem_mgr (gv: globals) (P: mpred): P |-- P * mem_mgr gv.
Proof. rewrite <- (sepcon_emp P) at 1. apply sepcon_derives; [apply derives_refl | apply create_mem_mgr]. Qed.

(* The test p == NULL on what malloc returned (a zero-size block: its token gives the valid pointer). *)
Lemma malloc_tc_test (t: type) (p: val) (P: mpred):
  0 <= sizeof t ->
  (if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p) * P
  |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof t)).
    + sep_apply (data_at__valid_ptr Ews t p); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews t p); [ lia | ]. entailer!.
Qed.

(* What malloc(m * sizeof(unsigned int)) returned, past the NULL test: an array of m elements (none when m = 0). *)
Lemma malloc_arr0_tuint (m: Z) (pc: val):
  0 <= m -> (pc <> nullval \/ m = 0) ->
  (if eq_dec pc nullval then emp else malloc_token Ews (tarray tuint m) pc * data_at_ Ews (tarray tuint m) pc)
  |-- arr0 Ews tuint m (Zrepeat Vundef m) pc * TT.
Proof.
  intros Hm Hpc. unfold arr0. destruct (eq_dec pc nullval).
  - destruct Hpc as [Hpc | ->]; [ contradiction | ]. rewrite if_true by auto. entailer!.
  - destruct (Z.eq_dec m 0); [ entailer! | ]. unfold data_at_, field_at_. entailer!.
Qed.

