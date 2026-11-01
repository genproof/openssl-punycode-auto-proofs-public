(* encode, one iteration of the pass over the code points for the code point n: the case c < n (delta++, with the
   return of 0 when delta exceeds maxint). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncPassLt.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncPassDefs.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Lemma tenc_pass_lt: forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl (f: nat) (n h0 B j delta bias h: Z)
  (out: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  4 * Zlength cps <= Int64.max_unsigned -> 0 <= room <= Int64.max_unsigned -> Zlength oinit = room ->
  0 <= j < Zlength cps -> 0 <= h0 <= Zlength cps -> 0 <= n <= maxint ->
  0 <= Znth j cps <= Int.max_unsigned -> Znth j cps < n ->
  encode cps = kont cps f n (sublist j (Zlength cps) cps) delta bias h B out ->
  h = h0 + cnt_eq n (sublist 0 j cps) -> 0 <= delta <= maxint -> 0 <= bias <= 2400 -> Zlength out <= room ->
  semax TDelta
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl))
   tstmt_passbody
   (overridePost (tpass_st shc pc cps sho po room oinit shl pl f n h0 B (j + 1) j)
      (tpost shc pc cps sho po room oinit shl pl)).
Proof.
  intros until out. intros H H0 H1 H2 H3 H4 H5 H6 H7 Hc Hlt Hk Hh Hd Hb Ho.
  pose proof (Zlength_nonneg out) as Hol.
  assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
  rewrite (sublist_next j (Zlength cps) cps) in Hk by lia.
  pose proof (cnt_eq_succ n cps j H5) as Hcnt.
  set (c := Znth j cps) in *.
  rewrite kont_lt in Hk by lia.
  unfold tstmt_passbody, tpass_st, tpost. abbreviate_semax.
  rewrite (arr0_ne shc tuint) by lia.
  forward.
  { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  forward_if (PROP (delta + 1 <= maxint)
    LOCAL (temp _t'13 (Vint (Int.repr c)); temp _n (Vlong (Int64.repr n));
      temp _delta (Vlong (Int64.repr (delta + 1))); temp _bias (Vlong (Int64.repr bias));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h)); temp _j__2 (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
      data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
  { forward.
    forward_if.
    + forward. rewrite uint_m1_long in *. fix_cmp. rewrite <- (arr0_ne shc tuint) by lia.
      apply tret0_entail; [ | apply bufv_len; lia].
      apply encode_fits_none. rewrite Hk. replace (maxint <? delta + 1) with true by lia. auto.
    + forward. entailer!. rewrite uint_m1_long in *. fix_cmp. lia. }
  { fix_cmp. lia. }
  Intros. replace (maxint <? delta + 1) with false in Hk by lia.
  forward.
  { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  forward_if.
  + rewrite Int.unsigned_repr in * by rep_lia. fix_eq64. lia.
  + forward. rewrite <- (arr0_ne shc tuint) by lia.
    Exists (delta + 1) bias h out. entailer!.
    rewrite Hcnt. replace (c =? n) with false by lia. lia.
Qed.
