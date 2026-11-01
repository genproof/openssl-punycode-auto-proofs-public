(* Piece 0 of the main of harness/api_a2ulabel_labels.c, its statement 10 (AlbP0Lib): the NULL test of the six blocks
   (a || chain of tests); main returns 0 when one is NULL, otherwise it continues at the cut before statement 11. *)
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

Lemma alb_p0_null : size_stmt -> null_stmt.
Proof.
  intros HS Espec gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po.
  unfold pre10, T10, ret0, main_post, Delta_main. abbreviate_semax. Intros.
  forward_if (temp _t'11 (Vint (Int.repr (if (isnull ps1 || isnull ps2)%bool then 1 else 0)))).
  { apply derives_trans with (ablk (len1 + 1) (vb bs1) ps1 * TT)%logic;
      [ cancel | apply ablk_tc_test; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with (ablk (len2 + 1) (vb bs2) ps2 * TT)%logic;
        [ cancel | apply ablk_tc_test; lia ]. }
    entailer!. unfold isnull. destruct (Val.eq ps1 nullval); [ contradiction | ].
    destruct (Val.eq ps2 nullval); [ subst; reflexivity | ].
    nonnull_cmp ps2. }
  forward_if (temp _t'12 (Vint (Int.repr (if (isnull ps1 || isnull ps2 || isnull pn)%bool then 1 else 0)))).
  { forward. entailer!. or_then. }
  { forward.
    { go_lower. apply derives_trans with (nblk (len1 + len2 + 2) pn * TT)%logic; [ cancel | unfold nblk; apply CmnLib.cmn_malloc_tc_test0; simpl; rep_lia ]. }
    entailer!. or_else pn. }
  forward_if (temp _t'13 (Vint (Int.repr (if (isnull ps1 || isnull ps2 || isnull pn || isnull po1)%bool then 1 else 0)))).
  { forward. entailer!. or_then. }
  { forward.
    { go_lower. apply derives_trans with (ablk (outlen1) (vb ob1) po1 * TT)%logic; [ cancel | apply ablk_tc_test; lia ]. }
    entailer!. or_else po1. }
  forward_if (temp _t'14 (Vint (Int.repr (if (isnull ps1 || isnull ps2 || isnull pn || isnull po1 || isnull po2)%bool then 1 else 0)))).
  { forward. entailer!. or_then. }
  { forward.
    { go_lower. apply derives_trans with (ablk (outlen2) (vb ob2) po2 * TT)%logic; [ cancel | apply ablk_tc_test; lia ]. }
    entailer!. or_else po2. }
  forward_if (temp _t'15 (Vint (Int.repr (if (isnull ps1 || isnull ps2 || isnull pn || isnull po1 || isnull po2 || isnull po)%bool then 1 else 0)))).
  { forward. entailer!. or_then. }
  { forward.
    { go_lower. apply derives_trans with (ablk (outlen1 + outlen2) (vb ob) po * TT)%logic; [ cancel | apply ablk_tc_test; lia ]. }
    entailer!. or_else po. }
  forward_if (pre11 gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. unfold pre11. entailer!. all_nonnull. }
  apply HS.
Qed.
