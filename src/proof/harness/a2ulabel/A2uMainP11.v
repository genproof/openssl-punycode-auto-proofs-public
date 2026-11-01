(* Piece 11 of the main of harness/x_a2ulabel.c: outlen, mode, out and want (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.

Lemma piece11 {Espec: OracleKind} gv v_k n bs sl pin psnap pcps:
  (forall outlen m, semax Delta_main (pre15 gv v_k n bs sl pin psnap pcps outlen m) S15then
     (overridePost (join16 gv v_k n bs sl pin psnap pcps outlen m) main_post)) ->
  (forall outlen m out want ob,
     semax Delta_main (pre16 gv v_k n bs sl pin psnap pcps outlen m out want ob) (Ssequence T16 ret0) main_post) ->
  semax Delta_main (pre11 gv v_k n bs sl pin psnap pcps) (Ssequence T11 ret0) main_post.
Proof.
  intros H15 H16. unfold pre11, T11, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call.
  Intros outlen.
  forward_call.
  Intros m.
  forward.
  forward.
  forward_if (join16 gv v_k n bs sl pin psnap pcps outlen m).
  - eapply semax_pre; [ | apply (H15 outlen m) ].
    unfold pre15. entailer!.
  - forward.
    unfold join16. Exists nullval nullval (Zrepeat 0 outlen). unfold pre16.
    unfold PunySpec.out_buf, want_buf. rewrite !if_true by auto.
    entailer!.
    split; [ unfold bytes_ok, Zrepeat; apply Forall_repeat; rep_lia | rewrite Zlength_Zrepeat; lia ].
  - unfold join16. Intros out want ob.
    eapply semax_pre; [ | apply (H16 outlen m out want ob) ].
    unfold pre16. entailer!.
Qed.
