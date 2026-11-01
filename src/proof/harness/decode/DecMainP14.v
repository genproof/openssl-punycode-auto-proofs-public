(* Piece 14 of the main of harness/x_decode.c: the checks of r and olen (pr_decode when len < UINT_MAX) (DecMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.proof.harness.decode.DecMainDefs.
Require OpensslPunycode.proof.punycode.DecModel OpensslPunycode.proof.harness.ARDecRange.
Local Open Scope logic.

Module RD := OpensslPunycode.proof.harness.RefDec.

(* The struct pr_dec is the same at the law's compspecs and at RefDec's. *)
Lemma data_at__dec_cs sh p: @data_at_ CS sh t_dec p = @data_at_ RD.CS sh t_dec p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at__change_composite CS RD.CS (CCE_any CS RD.CS)); reflexivity.
Qed.

Lemma data_at_dec_cs sh (v: val * val) p:
  @data_at CS sh t_dec v p = @data_at RD.CS sh t_dec v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite CS RD.CS (CCE_any CS RD.CS)); [apply JMeq_refl | reflexivity].
Qed.

Lemma piece14 : piece15_stmt -> piece14_stmt.
Proof.
  intros H15 Espec gv vc vo vd bs pe ps init po pw. unfold pre14, T14, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward_if (pre15 gv vc vo vd bs pe ps init po pw).
  - assert (Hd: dres bs init = (0, vb init, Zlength init)).
    { unfold dres, OpensslPunycode.proof.punycode.PunySpec.decode_result.
      rewrite (proj2 (Z.leb_le _ _)) by (change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned in H3; lia).
      reflexivity. }
    rewrite Hd. simpl fst. simpl snd.
    forward_call (Int.repr 1).
    forward. forward.
    forward_call (Int.repr 1).
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    unfold pre15. rewrite Hd. simpl fst. entailer!.
  - assert (Hlt: Zlength bs < Int.max_unsigned)
      by (change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned in H3; lia).
    destruct (decode bs (Zlength init)) as [ok out] eqn:HD.
    pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range bs (Zlength init) H (Zlength_nonneg _))
      as [Hr Hl]. rewrite HD in Hr, Hl. simpl in Hr, Hl.
    pose proof (OpensslPunycode.proof.punycode.DecModel.decode_result_eq bs (Zlength init) (vb init) ok out Hlt HD)
      as Hd. fold (dres bs init) in Hd.
    rewrite Hd. simpl fst. simpl snd.
    forward.
    rewrite (arr0_tuchar_cs CS RD.CS Ews (Zlength bs) _ ps).
    rewrite (arr0_tuint_cs CS RD.CS Ews (Zlength init) _ pw).
    rewrite (data_at__dec_cs Tsh vd).
    forward_call (Ews, ps, bs, Ews, pw, Zlength init, vb init, Tsh, vd).
    { unfold vb. apply Zlength_map. }
    rewrite HD. simpl fst. simpl snd.
    rewrite <- (arr0_tuchar_cs CS RD.CS Ews (Zlength bs) _ ps).
    rewrite <- (arr0_tuint_cs CS RD.CS Ews (Zlength init) _ pw).
    rewrite <- (data_at_dec_cs Tsh _ vd).
    forward.
    assert (Hlo: 0 <= Zlength out) by apply Zlength_nonneg.
    destruct ok.
    + forward_if.
      * forward_call (Int.repr 1).
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
        unfold pre15. rewrite Hd. simpl fst. entailer!.
      * discriminate.
    + forward_if.
      * contradiction.
      * forward_call (Int.repr 1).
        forward. forward.
        forward_call (Int.repr 1).
        { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
        unfold pre15. rewrite Hd. simpl fst. entailer!.
  - apply H15.
Qed.