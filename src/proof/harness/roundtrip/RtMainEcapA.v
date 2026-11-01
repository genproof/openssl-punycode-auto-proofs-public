(* Helpers of MainEcap.v (piece_ecap): the tail of stmt_ecap from the call of pr_encode. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.

Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Local Open Scope logic.

(* The octet arrays do not depend on the compspecs. *)
Lemma data_at_arr0_tuchar (cs1 cs2: compspecs) sh n v p:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v p = @arr0 cs2 sh tuchar n v p.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

(* The buffer lab cut into its 4 octets, the room of the encoding and its last octet. *)
Lemma lab_split3 (sh: share) (m: Z) (v: list val) (p: val):
  0 <= m -> Zlength v = 16 * m + 6 -> field_compatible (tarray tuchar (16 * m + 6)) [] p ->
  data_at sh (tarray tuchar (16 * m + 6)) v p =
  data_at sh (tarray tuchar 4) (sublist 0 4 v) p *
  data_at sh (tarray tuchar (16 * m + 1)) (sublist 4 (16 * m + 5) v) (offset_val 4 p) *
  data_at sh (tarray tuchar 1) (sublist (16 * m + 5) (16 * m + 6) v) (offset_val (16 * m + 5) p).
Proof.
  intros Hm Hv Hf.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh (16 * m + 6) 4 (16 * m + 5)) by lia.
  rewrite !field_address0_offset.
  2, 3: apply arr_field_compatible0; auto; lia.
  simpl. replace (16 * m + 5 - 4) with (16 * m + 1) by lia. replace (16 * m + 6 - (16 * m + 5)) with 1 by lia.
  rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
Qed.

(* forward_call of pr_encode (a spec at RefRt's compspecs) asks for this. *)
#[local] Instance ecap_CCE : change_composite_env OpensslPunycode.proof.harness.RefRt.CS CS := CCE_any _ _.

(* The tail of stmt_ecap after the NULL test of lab: the call of pr_encode, its test, then stmt_mallocs. *)
Definition stmt_ecap_enc : statement :=
  match stmt_ecap with Ssequence _ (Ssequence _ (Ssequence _ s)) => s | _ => Sskip end.

Lemma ecap_encode : piece_mallocs_stmt ->
  forall (Espec: OracleKind) gv cps pc vo ve plab,
    Zlength cps <= 512 -> Forall (fun c => 0 <= c <= 1114111) cps ->
    semax Delta_main
    (PROP (plab <> nullval)
    LOCAL (temp _lab plab; temp _ecap (Vlong (Int64.repr (16 * Zlength cps + 1)));
      temp _ulen (Vlong (Int64.repr (ulen_of cps)));
      temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0)));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (16 * Zlength cps + 6)) plab;
      data_at_ Ews (tarray tuchar (16 * Zlength cps + 6)) plab;
      arr0 Ews tuint (Zlength cps) (vb cps) pc; data_at_ Tsh tuint vo;
      data_at_ Tsh tulong ve; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
      OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; TT))
    stmt_ecap_enc main_ret.
Proof.
  intros H Espec gv cps pc vo ve plab H0 H1.
  assert (Hm: 0 <= Zlength cps) by apply Zlength_nonneg.
  unfold stmt_ecap_enc, stmt_ecap. cbv iota. unfold main_ret, main_post. abbreviate_semax.
  Intros.
  assert_PROP (field_compatible (tarray tuchar (16 * Zlength cps + 6)) [] plab) by entailer!.
  rewrite data_at__tarray.
  rewrite (lab_split3 Ews (Zlength cps)) by (auto; rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia.
  replace (16 * Zlength cps + 5 - 4) with (16 * Zlength cps + 1) by lia.
  rewrite (data_at_arr0_tuchar CS OpensslPunycode.proof.harness.RefRt.CS Ews (16 * Zlength cps + 1)) by lia.
  rewrite (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS).
  Intros.
  forward_call (Ews, pc, cps, Ews, offset_val 4 plab, 16 * Zlength cps + 1, Zrepeat (default_val tuchar) (16 * Zlength cps + 1), Tsh, ve).
  { split. { eapply Forall_impl; [ | exact H1 ]. intros c Hc. simpl in Hc. rep_lia. }
    rewrite Zlength_Zrepeat; lia. }
  Intros o'.
  destruct (OpensslPunycode.proof.harness.RefRt.encode_fits cps (16 * Zlength cps + 1)) eqn:Hfit.
  2: forward_if; [ forward; Exists (Int.repr 0); entailer! | now elim H5 ].
  unfold OpensslPunycode.proof.harness.RefRt.encode_fits in Hfit.
  unfold OpensslPunycode.proof.harness.RefRt.encode_out, OpensslPunycode.proof.harness.RefRt.encode_len.
  destruct (encode cps) as [e|] eqn:He; [ | discriminate ].
  rewrite Hfit. rename Hfit into Hle.
  forward_if; [ discriminate | ].
  apply Z.leb_le in Hle.
  eapply semax_pre; [ | apply (H Espec gv cps e pc plab vo ve) ].
  unfold P_mallocs, main_frame.
  rewrite <- (data_at_arr0_tuchar CS OpensslPunycode.proof.harness.RefRt.CS Ews (16 * Zlength cps + 1)) by lia.
  rewrite <- (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS).
  assert (Hl: Zlength (lab_after_encode (Zlength cps) e) = 16 * Zlength cps + 6).
  { unfold lab_after_encode, vb. list_solve. }
  rewrite (lab_split3 Ews (Zlength cps) (lab_after_encode (Zlength cps) e)) by auto.
  replace (sublist 0 4 (lab_after_encode (Zlength cps) e)) with (Zrepeat (default_val tuchar) (4 - 0))
    by (unfold lab_after_encode, vb; list_solve).
  replace (sublist 4 (16 * Zlength cps + 5) (lab_after_encode (Zlength cps) e)) with
    (vb e ++ sublist (Zlength e) (16 * Zlength cps + 1) (Zrepeat (default_val tuchar) (16 * Zlength cps + 1)))
    by (unfold lab_after_encode, vb; list_solve).
  replace (sublist (16 * Zlength cps + 5) (16 * Zlength cps + 6) (lab_after_encode (Zlength cps) e)) with
    (Zrepeat (default_val tuchar) (16 * Zlength cps + 6 - (16 * Zlength cps + 5)))
    by (unfold lab_after_encode, vb; list_solve).
  entailer!.
Qed.
