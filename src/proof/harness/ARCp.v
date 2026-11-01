(* pr_a2ulabel, an ACE label decoded into cps: the loop writing the UTF-8 form of each code point (pr_utf8 into the
   local u, pr_put); a code point above 0x10FFFF returns -1 (the model's put_utf8s fails). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Require Import OpensslPunycode.proof.harness.ARDecRange.
Require Import OpensslPunycode.proof.harness.ARCpLib.
Local Open Scope logic.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

(* The code-point loop: _j holds j, the model has written the code points before jm with the sink k1. *)
Definition cp_inv (cps: list Z) (j jm: Z) (k1: sink) : environ -> mpred :=
  PROP (0 <= jm <= Zlength cps; put_utf8s cap k cps = put_utf8s cap k1 (sublist jm (Zlength cps) cps);
        sink_ok cap k1)
  LOCAL (temp _j (Vlong (Int64.repr j)); temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u;
       data_at Tsh t_decA (Vint (Int.repr 1), Vlong (Int64.repr (Zlength cps))) v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k1) pk;
       sink_buf shb buf cap init (fst k1);
       data_at shc (tarray tuint label_cap) (vb cps ++ sublist (Zlength cps) label_cap cv) pc).

Lemma cp_piece: forall cps,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  is_ace (lab s st) = true ->
  Zlength (sublist (st + 4) (lab_end s st) s) < maxint ->
  decode (sublist (st + 4) (lab_end s st) s) label_cap = (true, cps) ->
  semax Delta_a2u (ace_mid shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv cps) s_cploop
    (overridePost (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k)
       (ar_RB shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u)).
Proof.
  intros cps Hctx Hit Hace Hlen Hdec. unfold ace_mid, lab_post, ar_RB, ar_post. abbreviate_semax.
  destruct Hctx as (Hshs & Hshk & Hshb & Hshc & Hbs & Hls & Hcap & Hinit & Hps).
  destruct Hit as (Hst & Hk & Hcv & HA).
  pose proof (cp_step s st cap k cps Hst Hace Hlen Hdec) as Hstep.
  pose proof (lab_end_range s st Hst) as He.
  destruct (decode_out_range (sublist (st + 4) (lab_end s st) s) label_cap) as [Hrng Hcl].
  { unfold bytes_ok in *. apply Forall_sublist; auto. }
  { unfold label_cap; lia. }
  rewrite Hdec in Hrng, Hcl. cbn [snd] in Hrng, Hcl.
  unfold s_cploop. forward.
  eapply semax_pre with (P' := EX j: Z, EX k1: sink, cp_inv cps j j k1).
  { Exists 0 k. unfold cp_inv. entailer!. rewrite sublist_same by lia. auto. }
  apply semax_loop with (Q' := EX j: Z, EX k1: sink, cp_inv cps j (j + 1) k1).
  - unfold cp_inv. Intros j k1. unfold s_cpbody.
    unfold t_decA. forward.
    change label_cap with 512 in Hcv, Hcl, Hdec |- *.
    forward_if.
    2:{ assert (j = Zlength cps) by lia. subst j. rewrite sublist_nil in H0. forward.
        Exists k1 (vb cps ++ sublist (Zlength cps) 512 cv). unfold t_decA. entailer!.
        rewrite Hstep, H0. reflexivity. }
    assert (Hc: 0 <= Znth j cps <= maxint) by (eapply Forall_Znth in Hrng; [exact Hrng | lia]).
    assert (Hz: @Znth val Vundef j (vb cps ++ sublist (Zlength cps) 512 cv) = Vint (Int.repr (Znth j cps))).
    { unfold vb. rewrite Znth_app1 by (rewrite Zlength_map; lia).
      change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite Znth_map by lia. reflexivity. }
    forward. { rewrite Hz. entailer!. }
    rewrite Hz. set (c := Znth j cps) in *. pose proof (utf8_len c) as Hul.
    sep_apply (u_split (Zlength (utf8 c)) v_u Hul). Intros.
    rewrite (arr0_tuchar_cs CS RefRt.CS Tsh (Zlength (utf8 c))).
    forward_call (c, Tsh, v_u, Zrepeat Vundef (Zlength (utf8 c))).
    { entailer!. simpl. rewrite Int.unsigned_repr by (unfold maxint in Hc; rep_lia). reflexivity. }
    { split; [unfold maxint in Hc; rep_lia | rewrite Zlength_Zrepeat; lia]. }
    rewrite (arr0_tuchar_cs RefRt.CS CS Tsh (Zlength (utf8 c))).
    forward.
    forward_if.
    + assert (Hn: Zlength (utf8 c) = 0).
      { apply (f_equal Int64.unsigned) in H3. rewrite Int64.unsigned_repr in H3 by rep_lia. exact H3. }
      assert (Hf: label_step cap k (lab s st) = (false, k1)).
      { rewrite Hstep, H0. apply put_utf8s_stop; auto; lia. }
      pose proof (cp_a2ulabel s cap (-1) k1 ltac:(rewrite <- HA; apply cp_fail; auto)) as HR.
      rewrite Hn. unfold arr0 at 1. unfold u_rest. simpl.
      forward.
      Exists (snd k1) (vb cps ++ sublist (Zlength cps) 512 cv). rewrite HR.
      destruct k1 as [w sh]. simpl. change label_cap with 512. entailer!.
    + assert (Hn: Zlength (utf8 c) <> 0) by (intro E; apply H3; rewrite E; reflexivity).
      assert (Hb: bytes_ok (utf8 c)) by (apply utf8_bytes; lia).
      assert (Hk2: sink_ok cap (put cap k1 (utf8 c))) by (apply put_ok; auto).
      assert (Hm: put_utf8s cap k cps = put_utf8s cap (put cap k1 (utf8 c)) (sublist (j + 1) (Zlength cps) cps)).
      { rewrite H0. apply put_utf8s_last; auto; lia. }
      destruct H1 as [Hk1 Hb1].
      forward_call (shk, pk, buf, cap, k1, init, shb, Tsh, v_u, utf8 c).
      Exists j (put cap k1 (utf8 c)).
      sep_apply (u_join (utf8 c) v_u ltac:(lia)).
      change label_cap with 512.
      entailer!.
  - unfold cp_inv. Intros j k1. unfold s_cpincr. forward.
    Exists (j + 1) k1. entailer!.
Qed.

End Piece.
