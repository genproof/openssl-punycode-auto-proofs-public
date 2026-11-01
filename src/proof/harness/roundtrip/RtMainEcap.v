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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainEcapA.
Local Open Scope logic.

Lemma piece_ecap : piece_mallocs_stmt -> piece_ecap_stmt.
Proof.
  intros H. unfold piece_ecap_stmt. intros.
  unfold P_ecap, stmt_ecap, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  assert (Hm: 0 <= Zlength cps) by apply Zlength_nonneg.
  forward.
  forward_call (tarray tuchar (16 * Zlength cps + 6), gv).
  { entailer!. simpl. rewrite Z.max_r by lia. unfold Vptrofs; simpl. do 3 f_equal. lia. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros plab.
  forward_if (PROP (plab <> nullval)
    LOCAL (temp _lab plab; temp _ecap (Vlong (Int64.repr (16 * Zlength cps + 1)));
      temp _ulen (Vlong (Int64.repr (ulen_of cps)));
      temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0)));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (16 * Zlength cps + 6)) plab;
      data_at_ Ews (tarray tuchar (16 * Zlength cps + 6)) plab;
      arr0 Ews tuint (Zlength cps) (vb cps) pc; data_at_ Tsh tuint vo;
      data_at_ Tsh tulong ve; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
      OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; TT)).
  { eapply derives_trans; [ | apply (malloc_tc_test (tarray tuchar (16 * Zlength cps + 6)) plab TT)];
      [ cancel | simpl; rep_lia ]. }
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. rewrite if_false by auto. entailer!. }
  apply (ecap_encode H); auto.
Qed.
