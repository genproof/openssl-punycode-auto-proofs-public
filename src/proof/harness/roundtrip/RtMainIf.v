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

Lemma piece_if : piece_lab_stmt -> piece_if_stmt.
Proof.
  intros HL. unfold piece_if_stmt. intros.
  unfold P_if, stmt_if, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  forward_if (Q_ret vo ve).
  - assert (OK: one_label_ok cps = true) by (destruct (one_label_ok cps); auto; contradiction H3; reflexivity).
    eapply semax_pre; [ | apply (HL Espec gv cps e pc plab vo ve) ].
    unfold P_lab, main_frame. entailer!.
  - forward. unfold Q_ret. entailer!.
  - unfold Q_ret. forward. Exists (Int.repr 0). entailer!.
Qed.
