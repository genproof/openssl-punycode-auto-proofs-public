(* Piece 0 of the main of harness/rfc_unique.c: len1, input1 = any_bytes(len1), len2, input2 = any_bytes(len2),
   cap = nondet_u32(), out1 and out2 = any_uints(cap) (RunMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunTac.
Local Open Scope logic.

Lemma piece0 : piece7_stmt -> piece0_stmt.
Proof.
  intros H7 Espec gv v1 v2. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (9223372036854775807).
  Intros len1.
  forward_call (len1, gv).
  Intros vret. destruct vret as [pi1 bs1]. simpl fst in *. simpl snd in *. subst len1.
  rewrite (@malloc_token_change_composite C.CS CS (CCE_any _ _) Ews (tarray tuchar _)) by reflexivity.
  rewrite (data_at_tuchar_cs C.CS CS).
  fold (mblock_uc (Zlength bs1) (vb bs1) pi1).
  forward_call (9223372036854775807).
  Intros len2.
  forward_call (len2, gv).
  Intros vret. destruct vret as [pi2 bs2]. simpl fst in *. simpl snd in *. subst len2.
  rewrite (@malloc_token_change_composite C.CS CS (CCE_any _ _) Ews (tarray tuchar _)) by reflexivity.
  rewrite (data_at_tuchar_cs C.CS CS).
  fold (mblock_uc (Zlength bs2) (vb bs2) pi2).
  forward_call tt.
  Intros c.
  forward_call (c, gv).
  Intros vret. destruct vret as [po1 vs1]. simpl fst in *. simpl snd in *.
  rewrite (@malloc_token_change_composite C.CS CS (CCE_any _ _) Ews (tarray tuint c)) by reflexivity.
  rewrite (data_at_tuint_cs C.CS CS).
  fold (mblock_ui c (vb vs1) po1).
  forward_call (c, gv).
  Intros vret. destruct vret as [po2 vs2]. simpl fst in *. simpl snd in *.
  rewrite (@malloc_token_change_composite C.CS CS (CCE_any _ _) Ews (tarray tuint c)) by reflexivity.
  rewrite (data_at_tuint_cs C.CS CS).
  fold (mblock_ui c (vb vs2) po2).
  eapply semax_pre; [ | apply (H7 Espec gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2) ].
  unfold pre7. entailer!.
Qed.
