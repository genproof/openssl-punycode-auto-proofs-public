(* Piece 0 of the main of harness/api_a2ulabel_labels.c, its statement 11 (AlbP0Lib): the test of outlen1, outlen2
   against 0; main returns 0 when one is 0, otherwise the state is pre12 of AlbMainDefs (the blocks unfolded, their
   malloc tokens dropped into TT) and main continues with piece 12. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbP0Lib.
Local Open Scope logic.

Lemma alb_p0_size : piece12_stmt -> size_stmt.
Proof.
  intros H12 Espec gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po.
  unfold pre11, T11, ret0, main_post, Delta_main. abbreviate_semax. Intros.
  forward_if (temp _t'16 (Vint (Int.repr (if (Z.eqb outlen1 0 || Z.eqb outlen2 0)%bool then 1 else 0)))).
  { forward. entailer!.
    match goal with Hz: Int64.repr _ = Int64.zero |- _ =>
      apply repr_inj_unsigned64 in Hz; [ rewrite Hz; reflexivity | rep_lia | rep_lia ] end. }
  { forward. entailer!.
    match goal with Hz: Int64.repr _ <> Int64.repr 0 |- _ =>
      assert (E1: (Zlength ob1 =? 0) = false) by (apply Z.eqb_neq; intros E; apply Hz; rewrite E; reflexivity) end.
    rewrite E1. simpl orb. unfold Int64.cmpu.
    destruct (Z.eqb_spec (Zlength ob2) 0) as [E2 | E2].
    - rewrite E2. reflexivity.
    - rewrite Int64.eq_false; [ reflexivity | ].
      intros E. apply repr_inj_unsigned64 in E; rep_lia. }
  forward_if (PROP (1 <= outlen1; 1 <= outlen2)
    LOCAL (temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
           temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
           temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
    SEP (mem_mgr gv; ablk (outlen1 + outlen2) (vb ob) po; ablk outlen2 (vb ob2) po2; ablk outlen1 (vb ob1) po1;
         nblk (len1 + len2 + 2) pn; ablk (len2 + 1) (vb bs2) ps2; ablk (len1 + 1) (vb bs1) ps1;
         PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    match goal with Hb: Int.repr (if ?B then 1 else 0) = Int.zero |- _ => apply int_flag_false in Hb end.
    rewrite Bool.orb_false_iff, !Z.eqb_neq in *. lia. }
  Intros. unfold ablk, nblk. rewrite !if_false by assumption. Intros.
  eapply semax_pre; [ | apply (H12 Espec gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po) ].
  unfold pre12. rewrite !(data_at_tuchar_cs H.CS CS).
  entailer!.
Qed.
