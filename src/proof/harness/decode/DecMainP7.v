(* Piece 7 of the main of harness/x_decode.c: bytes, the mallocs of out and want, their NULL test (DecMainDefs). *)
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
Require Import OpensslPunycode.proof.harness.decode.DecMainP7b.
Local Open Scope logic.

Lemma piece7 : piece11_stmt -> piece7_stmt.
Proof.
  intros H11 Espec gv vc vo vd bs pe ps c. unfold pre7, T7, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward. forward.
  forward_call (tarray tuint c, gv).
  { entailer!. simpl. rewrite Z.max_r by lia. rewrite Z.mul_comm. reflexivity. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros po.
  forward_call (tarray tuint c, gv).
  { entailer!. simpl. rewrite Z.max_r by lia. rewrite Z.mul_comm. reflexivity. }
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros pw.
  eapply semax_pre; [ | apply (piece7_test H11 Espec gv vc vo vd bs pe ps c po pw) ].
  unfold pre10. entailer!.
Qed.