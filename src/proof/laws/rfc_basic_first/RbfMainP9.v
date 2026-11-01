(* Piece 9 of the main of harness/rfc_basic_first.c: when r == 1, the loop over the output that matches its code
   points below 0x80 with the literal octets, the final check next == literal, then return 0 (RbfMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.harness.ARDecRange.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfModel.
Require Import OpensslPunycode.harness.rfc_basic_first.code.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfMainDefs.
Local Open Scope logic.

Lemma piece9 : piece9_stmt.
Proof.
  intros Espec gv vc bs pi cap po r a cnt. unfold pre8, T9, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  pose proof (DecModel.last_delim_range bs) as Hb. pose proof (Zlength_nonneg bs).
  assert (Hbl: last_delim bs <= Zlength bs) by lia.
  forward_if (PROP () LOCAL (lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
  - destruct H2 as [Hr01 [_ Hr1]].
    assert (r = 1) by (destruct Hr01; subst; [ discriminate | reflexivity ]). subst r.
    destruct (Hr1 eq_refl) as [out [tail [D [-> ->]]]]. clear Hr1 Hr01.
    pose proof (rbf_ok_filter bs cap out D) as Hf.
    pose proof (ARDecRange.decode_out_range bs cap H ltac:(lia)) as [Hrange Hlen]. rewrite D in Hrange, Hlen.
    simpl in Hrange, Hlen.
    pose proof (Zlength_nonneg out).
    forward. forward.
    forward_loop
      (EX j: Z, PROP (0 <= j <= Zlength out)
        LOCAL (temp _j (Vint (Int.repr j));
               temp _next (Vlong (Int64.repr (Zlength (filter lt128 (sublist 0 j out)))));
               temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po; temp _input pi;
               gvars gv; lvar _count tuint vc)
        SEP (arr0 Ews tuint cap (vb out ++ tail) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
             data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; TT))
    continue:
      (EX j: Z, PROP (0 <= j < Zlength out)
        LOCAL (temp _j (Vint (Int.repr j));
               temp _next (Vlong (Int64.repr (Zlength (filter lt128 (sublist 0 (j + 1) out)))));
               temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po; temp _input pi;
               gvars gv; lvar _count tuint vc)
        SEP (arr0 Ews tuint cap (vb out ++ tail) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
             data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; TT))
    break:
      (PROP ()
        LOCAL (temp _next (Vlong (Int64.repr (Zlength (filter lt128 out))));
               temp _literal (Vlong (Int64.repr (last_delim bs))); lvar _count tuint vc)
        SEP (data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; TT)).
    + Exists 0. entailer!.
    + Intros j. forward.
      forward_if (PROP (j < Zlength out)
        LOCAL (temp _j (Vint (Int.repr j));
               temp _next (Vlong (Int64.repr (Zlength (filter lt128 (sublist 0 j out)))));
               temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po; temp _input pi;
               gvars gv; lvar _count tuint vc)
        SEP (arr0 Ews tuint cap (vb out ++ tail) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
             data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; TT)).
      * forward. entailer!.
      * forward. entailer!. assert (j = Zlength out) by lia. subst j. rewrite sublist_same by lia. reflexivity.
      * Intros.
        assert (Hcap: cap <> 0) by lia.
        assert (Hx: 0 <= Znth j out <= Int.max_unsigned)
          by (rewrite Forall_Znth in Hrange; specialize (Hrange j ltac:(lia)); unfold maxint in Hrange; rep_lia).
        unfold arr0 at 1. rewrite if_false by exact Hcap.
        forward.
        { entailer!. rewrite app_Znth1 by (rewrite Zlength_vb; lia). unfold vb. rewrite Znth_map by lia. simpl. auto. }
        rewrite app_Znth1 by (rewrite Zlength_vb; lia). unfold vb at 1. rewrite Znth_map by lia.
        pose proof (Zlength_nonneg (filter lt128 (sublist 0 j out))) as Hk0.
        forward_if (PROP ()
          LOCAL (temp _j (Vint (Int.repr j));
                 temp _next (Vlong (Int64.repr (Zlength (filter lt128 (sublist 0 (j + 1) out)))));
                 temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po; temp _input pi;
                 gvars gv; lvar _count tuint vc)
          SEP (data_at Ews (tarray tuint cap) (vb out ++ tail) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
               data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; TT)).
        -- destruct (rbf_filter_prefix out (sublist 0 (last_delim bs) bs) j Hf ltac:(lia) ltac:(lia)) as [Hk Hkv].
           rewrite rbf_lit_len in Hk. rewrite rbf_lit_znth in Hkv by lia.
           forward_if (temp _t'8 (Vint Int.one)).
           ++ forward.
              { entailer!. rewrite app_Znth1 by (rewrite Zlength_vb; lia). unfold vb. rewrite Znth_map by lia. simpl. auto. }
              rewrite app_Znth1 by (rewrite Zlength_vb; lia). unfold vb at 1. rewrite Znth_map by lia.
              unfold arr0. rewrite if_false by lia.
              assert (Hi: 0 <= Znth (Zlength (filter lt128 (sublist 0 j out))) bs <= 255)
                by (unfold bytes_ok in H; rewrite Forall_Znth in H; apply H; lia).
              forward.
              { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
              unfold vb at 1. rewrite Znth_map by lia.
              forward.
              entailer!. unfold arr0. rewrite if_false by lia. cancel.
           ++ exfalso. lia.
           ++ forward_call (Int.one). forward.
              rewrite rbf_filter_step by lia.
              destruct (Znth j out <? 128) eqn:E; [ | apply Z.ltb_ge in E; lia ].
              rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
        -- forward. rewrite rbf_filter_step by lia.
           destruct (Znth j out <? 128) eqn:E; [ apply Z.ltb_lt in E; lia | ]. rewrite app_nil_r. entailer!.
        -- Exists j. entailer!. unfold arr0. rewrite if_false by assumption. cancel.
    + Intros j. forward. Exists (j + 1). entailer!.
    + rewrite Hf, rbf_lit_len. forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      entailer!.
  - forward. entailer!.
  - forward. Exists (Int.repr 0). entailer!.
Qed.
