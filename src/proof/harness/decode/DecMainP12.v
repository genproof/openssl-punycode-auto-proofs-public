(* Piece 12 of the main of harness/x_decode.c: olen = cap, r = ossl_punycode_decode(..) (DecMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.proof.harness.decode.DecMainDefs.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

Lemma piece12 : piece14_stmt -> piece12_stmt.
Proof.
  intros H14 Espec gv vc vo vd bs pe ps init po pw. unfold pre12, T12, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward. forward.
  rewrite (arr0_tuchar_cs CS PS.CS Ews (Zlength bs) _ pe).
  rewrite (arr0_tuint_cs CS PS.CS Ews (Zlength init) _ po).
  rewrite (data_at_cs_tuint CS PS.CS Tsh _ vo).
  forward_call (gv, Ews, pe, bs, Ews, po, Zlength init, vb init, Tsh, vo).
  { unfold vb. rewrite Zlength_map. reflexivity. }
  rewrite <- (arr0_tuchar_cs CS PS.CS Ews (Zlength bs) _ pe).
  rewrite <- (arr0_tuint_cs CS PS.CS Ews (Zlength init) _ po).
  rewrite <- (data_at_cs_tuint CS PS.CS Tsh _ vo).
  eapply semax_pre; [ | apply (H14 Espec gv vc vo vd bs pe ps init po pw) ].
  unfold pre14, dres. entailer!.
Qed.
