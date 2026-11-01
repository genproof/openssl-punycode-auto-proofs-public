(* pr_a2ulabel, an ACE label: the length check, pr_decode of its rest into cps (the local struct pr_dec d), the
   test of d.ok; a failure returns -1 (the model's label_step fails); then the continuation c with the code points. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.ARAce1Lib.
Local Open Scope logic.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma ace1_piece: forall c,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  is_ace (lab s st) = true ->
  (forall cps, Zlength (sublist (st + 4) (lab_end s st) s) < maxint ->
     decode (sublist (st + 4) (lab_end s st) s) label_cap = (true, cps) ->
     semax Delta_a2u (ace_mid shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv cps) c
       (overridePost (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k)
          (ar_RB shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u))) ->
  semax Delta_a2u (lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv)
    (Ssequence s_acechk (Ssequence s_call (Ssequence s_okchk c)))
    (overridePost (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k)
       (ar_RB shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u)).
Proof.
  intros c Hctx Hit Hace Hc. unfold lab_pre, ar_RB, ar_post. abbreviate_semax.
  destruct Hctx as (Hshs & Hshk & Hshb & Hshc & Hbs & Hls & Hcap & Hinit & Hps).
  destruct Hit as (Hst & Hk & Hcv & HA).
  pose proof (lab_end_range s st Hst) as He.
  assert (Hll: Zlength (lab s st) = lab_end s st - st) by (unfold lab; rewrite Zlength_sublist; lia).
  assert (H4: 4 <= lab_end s st - st).
  { unfold is_ace in Hace. rewrite <- Hll. destruct (4 <=? Zlength (lab s st)) eqn:E; [lia | discriminate]. }
  pose proof (ace1_rest s st Hst H4) as Hrest.
  set (rest := sublist (st + 4) (lab_end s st) s) in *.
  assert (Hlr: Zlength rest = lab_end s st - st - 4) by (unfold rest; rewrite Zlength_sublist; lia).
  unfold s_acechk.
  forward_if.
  - rewrite sub64_repr in H. rewrite !Int64.unsigned_repr in H by rep_lia.
    assert (Hf: label_step cap k (lab s st) = (false, k)).
    { unfold label_step. rewrite Hace, Hrest. replace (maxint <=? Zlength rest) with true by (symmetry; apply Z.leb_le; unfold maxint; lia). reflexivity. }
    pose proof (ace1_a2ulabel s cap (-1) k ltac:(rewrite <- HA; apply ace1_fail; auto)) as HR.
    forward.
    Exists (snd k) cv. rewrite HR. destruct k as [w sh]. simpl. unfold t_decA. entailer!.
  - rewrite sub64_repr in H. rewrite !Int64.unsigned_repr in H by rep_lia.
    assert_PROP (0 < Zlength s -> field_compatible (tarray tuchar (Zlength s)) [] ps) as Hfc.
    { unfold arr0. destruct (Z.eq_dec (Zlength s) 0); entailer!. }
    rewrite (ace1_split3 shs (Zlength s) (st + 4) (lab_end s st) s ps) by (auto; lia).
    fold rest. replace (lab_end s st - (st + 4)) with (Zlength rest) by lia.
    rewrite (arr0_tuchar_cs CS RefDec.CS shs (Zlength rest) (vb rest) (offset_val (st + 4) ps)).
    rewrite <- ace1_cps.
    rewrite ace1_dec_.
    unfold s_call. Intros.
    forward_call (shs, offset_val (st + 4) ps, rest, shc, pc, 512, cv, Tsh, v_d).
    { entailer!. destruct ps; try contradiction. simpl. rewrite Hlr. reflexivity. }
    { unfold rest, bytes_ok in *. apply Forall_sublist; auto. }
    change label_cap with 512 in Hc.
    destruct (decode rest 512) as [ok cps] eqn:Hd. cbn [fst snd].
    rewrite ace1_dec, ace1_cps.
    rewrite (arr0_tuchar_cs RefDec.CS CS shs (Zlength rest) (vb rest) (offset_val (st + 4) ps)).
    unfold s_okchk. forward.
    destruct ok.
    + forward_if.
      { inv H0. }
      eapply semax_pre; [ | apply (Hc cps); [unfold maxint; lia | reflexivity] ].
      unfold ace_mid. rewrite (ace1_split3 shs (Zlength s) (st + 4) (lab_end s st) s ps) by (auto; lia).
      fold rest. replace (lab_end s st - (st + 4)) with (Zlength rest) by lia.
      change label_cap with 512. entailer!.
    + assert (Hf: label_step cap k (lab s st) = (false, k)).
      { unfold label_step. rewrite Hace, Hrest.
        replace (maxint <=? Zlength rest) with false by (symmetry; apply Z.leb_gt; unfold maxint; lia).
        change label_cap with 512. rewrite Hd. reflexivity. }
      pose proof (ace1_a2ulabel s cap (-1) k ltac:(rewrite <- HA; apply ace1_fail; auto)) as HR.
      forward_if.
      * forward.
        Exists (snd k) (vb cps ++ sublist (Zlength cps) 512 cv). rewrite HR.
        rewrite (ace1_split3 shs (Zlength s) (st + 4) (lab_end s st) s ps) by (auto; lia).
        replace (lab_end s st - (st + 4)) with (Zlength (sublist (st + 4) (lab_end s st) s)) by lia.
        destruct k as [w sh]. simpl. unfold t_decA. entailer!.
      * exfalso; apply H0; reflexivity.
Qed.

End Piece.
