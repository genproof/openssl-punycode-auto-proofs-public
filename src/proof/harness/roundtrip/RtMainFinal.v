(* A piece of the main of harness/x_roundtrip.c (see MainDefs.v). *)
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainFinalA.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainFinalB.

Lemma piece_final : decode_encode_stmt -> encode_chars_stmt -> a2u_model_stmt -> piece_final_stmt.
Proof.
  intros DE EC AM. unfold piece_final_stmt. intros.
  unfold P_final, stmt_lab_final, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  destruct (utf8s_ok cps H0) as [Hu8 Hu8len].
  assert (Hul: 1 <= ulen_of cps <= 2049) by (unfold ulen_of; pose proof (Zlength_nonneg (utf8s cps)); lia).
  forward.
  { entailer!. unfold ulen_of in *. lia. }
  replace (upd_Znth (Zlength (utf8s cps)) (vb (utf8s cps) ++ [Vundef]) (Vint (Int.zero_ext 8 (Int.repr 0))))
    with (vb (utf8s cps ++ [0])) by (rewrite vb_app; unfold vb at 2; simpl; rewrite upd_Znth_app2 by
      (rewrite Zlength_vb; list_solve); rewrite Zlength_vb, Z.sub_diag; reflexivity).
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(data_at_cs_tint OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite !(data_at_cs_tlong OpensslPunycode.proof.shim.ShimSpec.CS CS).
  Intros.
  forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  gather_SEP 7 8 9.
  replace_SEP 0 (OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0).
  { entailer!. unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(data_at_cs_tint OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite !(data_at_cs_tlong OpensslPunycode.proof.shim.ShimSpec.CS CS). cancel. }
  assert_PROP (isptr pu) by entailer!.
  replace_SEP 2 (OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pu (ulen_of cps) (Zrepeat Vundef (ulen_of cps))
                   (tarray tuchar 0)).
  { unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
    destruct pu; try contradiction. rewrite if_false by discriminate. rewrite if_false by lia.
    rewrite sepcon_emp. rewrite data_at__tarray. entailer!. }
  pose proof (str_ok_ace cps e H0 H1 H3 EC) as Hstr.
  forward_call (gv, Ews, plab, ace e, Ews, pu, ulen_of cps, Zrepeat Vundef (ulen_of cps), tarray tuchar 0, 0, 0, 0).
  { split; [ right; apply Zlength_Zrepeat; lia | ].
    unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds. rep_lia. }
  Intros mf.
  assert (Hoc: OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pu (ulen_of cps) (ace e) (Zrepeat Vundef (ulen_of cps)) 0 0 mf
     = if mf then (-1, 0, 1, Zrepeat Vundef (ulen_of cps)) else (1, 0, 0, vb (utf8s cps ++ [0]))).
  { unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome.
    destruct pu; try contradiction. rewrite if_false by discriminate.
    replace (ulen_of cps =? 0) with false by lia. simpl. destruct mf; [ reflexivity | ].
    rewrite (AM cps e) by auto. f_equal. replace (Zlength (utf8s cps ++ [0])) with (ulen_of cps)
      by (unfold ulen_of; list_solve). rewrite sublist_nil, app_nil_r. reflexivity. }
  rewrite Hoc. clear Hoc DE EC AM.
  destruct mf; cbn [fst snd].
  2: { apply (final_tail_ok gv cps e plab pu pw vo ve); auto. }
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(data_at_cs_tint OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite !(data_at_cs_tlong OpensslPunycode.proof.shim.ShimSpec.CS CS).
  Intros.
  forward.
  forward_if True.
  { first [ discriminate | contradiction ]. }
  { forward_call. entailer!. }
  forward. forward_call. unfold Q_ret. entailer!.
Qed.
