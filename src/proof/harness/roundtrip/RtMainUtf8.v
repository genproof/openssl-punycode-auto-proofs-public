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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainUtf8A.
Local Open Scope logic.

Lemma piece_utf8 : piece_final_stmt -> piece_utf8_stmt.
Proof.
  intros H. unfold piece_utf8_stmt; intros.
  unfold P_utf8, stmt_lab_utf8, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  assert (Hlen := utf8s_len_bound cps H1).
  forward_for_simple_bound (Zlength cps)
    (EX j: Z,
     PROP ()
     LOCAL (temp _at (Vlong (Int64.repr (Zlength (utf8s (sublist 0 j cps))))); temp _want pw; temp _u pu;
            temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps))); temp _cps pc;
            temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
     SEP (data_at Ews (tarray tuchar (ulen_of cps))
            (vb (utf8s (sublist 0 j cps)) ++ Zrepeat Vundef (ulen_of cps - Zlength (utf8s (sublist 0 j cps)))) pw;
          data_at_ Ews (tarray tuchar (ulen_of cps)) pu;
          OpensslPunycode.proof.shim.ShimSpec.cstr Ews (ace e) plab;
          arr0 Ews tuint (Zlength cps) (vb cps) pc;
          data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo;
          data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
          OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT)).
  - rewrite sublist_nil. change (utf8s []) with (@nil Z). rewrite Zlength_nil, Z.sub_0_r. simpl vb.
    rewrite app_nil_l. entailer!.
  - unfold arr0 at 1. rewrite if_false by lia.
    assert (Hc: 0 <= Znth i cps <= 1114111) by (eapply Forall_Znth; eauto; lia).
    assert (Hz: Znth i (vb cps) = Vint (Int.repr (Znth i cps))) by (unfold vb; rewrite Znth_map by lia; auto).
    pose proof (utf8_len _ Hc) as Hk.
    pose proof (utf8s_step_len cps i H5) as Hs.
    pose proof (utf8s_step cps i H5) as Hst.
    forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. exact I. }
    match goal with |- context [temp _t'21 ?x] =>
      replace x with (Vint (Int.repr (Znth i cps))) by (rewrite <- Hz; reflexivity) end.
    sep_apply (split_want (cs2 := OpensslPunycode.proof.harness.RefRt.CS) Ews (ulen_of cps)
      (Zlength (utf8s (sublist 0 i cps))) (Zlength (utf8 (Znth i cps))) (vb (utf8s (sublist 0 i cps))) pw).
    { unfold ulen_of. pose proof (Zlength_nonneg (utf8s (sublist 0 i cps))). lia. }
    { lia. }
    { unfold ulen_of; lia. }
    { unfold vb; rewrite Zlength_map; auto. }
    Intros.
    forward_call (Znth i cps, Ews, offset_val (Zlength (utf8s (sublist 0 i cps))) pw,
                  Zrepeat Vundef (Zlength (utf8 (Znth i cps)))).
    { rewrite Zlength_Zrepeat; lia. }
    forward.
    sep_apply (join_want (cs2 := OpensslPunycode.proof.harness.RefRt.CS) Ews (ulen_of cps)
      (Zlength (utf8s (sublist 0 i cps))) (Zlength (utf8 (Znth i cps))) (vb (utf8s (sublist 0 i cps)))
      (vb (utf8 (Znth i cps))) pw).
    { unfold ulen_of. pose proof (Zlength_nonneg (utf8s (sublist 0 i cps))). lia. }
    { lia. }
    { unfold ulen_of; lia. }
    { unfold vb; rewrite Zlength_map; auto. }
    { unfold vb; rewrite Zlength_map; auto. }
    rewrite Hst, vb_app, Zlength_app. unfold arr0. rewrite if_false by lia.
    entailer!.
  - rewrite sublist_same by lia.
    eapply semax_pre; [ | apply (H Espec gv cps e plab pu pw vo ve) ].
    unfold P_final, main_frame.
    replace (ulen_of cps - Zlength (utf8s cps)) with 1 by (unfold ulen_of; lia).
    entailer!.
Qed.
