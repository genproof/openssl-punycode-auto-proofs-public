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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLabA.

Lemma piece_lab : encode_chars_stmt -> piece_utf8_stmt -> piece_lab_stmt.
Proof.
  intros _ HU. unfold piece_lab_stmt. intros.
  unfold P_lab, stmt_lab, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  assert (Hm: 0 <= Zlength cps) by apply Zlength_nonneg.
  assert (He: 0 <= Zlength e) by apply Zlength_nonneg.
  forward. forward. forward. forward.
  forward. forward.
  pose proof (ulen_of_bounds cps).
  rewrite lab_ace by lia.
  assert (Hsz: sizeof (tarray tuchar (ulen_of cps)) = ulen_of cps).
  { simpl. rewrite Z.max_r by lia. lia. }
  forward_call (tarray tuchar (ulen_of cps), gv).
  Intros pu.
  forward_call (tarray tuchar (ulen_of cps), gv).
  Intros pw.
  eapply semax_pre; [ | apply (lab_test HU Espec gv cps e pc plab pu pw vo ve) ].
  unfold P_lab_test. entailer!.
Qed.
