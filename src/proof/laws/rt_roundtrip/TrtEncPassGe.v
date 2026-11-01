(* encode, one iteration of the pass over the code points for the code point n: the case n <= c (the digits of
   delta when c == n, given by the statement tdig_ok of that branch; nothing when n < c). *)
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

Lemma tenc_pass_ge: forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl (f: nat) (n h0 B j delta bias h: Z)
  (out: list Z),
  tdig_ok ->
  readable_share shc -> writable_share sho -> writable_share shl ->
  4 * Zlength cps <= Int64.max_unsigned -> 0 <= room <= Int64.max_unsigned -> Zlength oinit = room ->
  0 <= j < Zlength cps -> 0 <= h0 <= Zlength cps -> 0 <= B <= Zlength cps -> 0 <= n <= maxint ->
  0 <= Znth j cps <= Int.max_unsigned -> n <= Znth j cps ->
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
  intros until out. intros Hdig H H0 H1 H2 H3 H4 H5 H6 HB H7 Hc Hge Hk Hh Hd Hb Ho.
  pose proof (Zlength_nonneg out) as Hol.
  pose proof (cnt_eq_nonneg n (sublist 0 j cps)) as Hcn0.
  pose proof (cnt_eq_le n (sublist 0 j cps)) as Hcl. rewrite Zlength_sublist in Hcl by lia.
  assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
  rewrite (sublist_next j (Zlength cps) cps) in Hk by lia.
  pose proof (cnt_eq_succ n cps j H5) as Hcnt.
  set (c := Znth j cps) in *.
  unfold tstmt_passbody, tpost. abbreviate_semax.
  rewrite (arr0_ne shc tuint) by lia.
  forward.
  { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  forward_if (PROP ()
    LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
      data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
  { fix_cmp. rewrite Int.unsigned_repr in * by rep_lia. lia. }
  { forward. entailer!. }
  forward.
  { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  rewrite <- (arr0_ne shc tuint) by lia.
  forward_if.
  + rewrite Int.unsigned_repr in * by rep_lia. fix_eq64.
    assert (Hcn: c = n) by assumption. rewrite Hcn in Hk. rewrite kont_eq in Hk.
    eapply semax_pre; [ | eapply semax_post; [ | | | | eapply (Hdig _ shc pc cps sho po room oinit shl pl
       n delta bias h B j out f (sublist (j + 1) (Zlength cps) cps)) ] ].
    { entailer!. }
    { rewrite !HoP. unfold tdig_q, tpass_st.
      Exists 0 (adapt delta (h + 1) (h =? B)) (h + 1) (out ++ enc_digits 64 delta 36 bias). entailer!.
      split; [rewrite Hcnt, Z.eqb_refl; lia | apply adapt_bound; lia]. }
    { apply brk_post. }
    { apply cont_post. }
    { intros. apply ENTAIL_refl. }
    all: auto; try lia.
  + assert (Hne: c <> n) by (intro E; match goal with H: Int64.repr _ <> Int64.repr n |- _ => apply H end;
      rewrite Int.unsigned_repr by rep_lia; rewrite E; reflexivity).
    rewrite kont_gt in Hk by lia.
    forward. unfold tpass_st. Exists delta bias h out. entailer!.
    rewrite Hcnt. replace (c =? n) with false by lia. lia.
Qed.
