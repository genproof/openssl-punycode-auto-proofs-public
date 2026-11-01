(* Piece 0 of the main of harness/api_decode_capacity.c: len drawn, input = any_bytes(len), cap drawn,
   out = any_uints(cap), saved = malloc(cap * 4) (DcapMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

Lemma piece0 : piece5_stmt -> piece0_stmt.
Proof.
  intros H5 Espec gv vc ve vf. unfold pre0, lvars3, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (9223372036854775807).
  Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [pi bs]. simpl fst in *. simpl snd in *.
  forward_call tt.
  Intros c.
  forward_call (c, gv).
  Intros vret. destruct vret as [po init]. simpl fst in *. simpl snd in *.
  forward_call (tarray tuint c, gv).
  { entailer!. simpl. unfold Vptrofs, Ptrofs.to_int64; simpl. rewrite Z.max_r by lia. do 3 f_equal. lia. }
  { simpl; rep_lia. }
  Intros ps.
  rewrite !(@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuchar _)) by reflexivity.
  rewrite !(@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuint _)) by reflexivity.
  rewrite !(data_at_tuchar_cs CM.CS CS).
  rewrite !(data_at_tuint_cs CM.CS CS).
  eapply semax_pre; [ | apply (H5 Espec gv vc ve vf bs pi c init po ps) ].
  unfold pre5, lvars3, mblock_uc, mblock_ui, mblock_un. entailer!.
Qed.
