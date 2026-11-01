(* Piece 0 of the main of harness/rfc_digit_case.c: len, the input, other (its copy), cap and the arrays out1, out2
   (RdcMainDefs); the NULL test that follows is piece 6 (RdcMainP6.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcModel.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainDefs.
Local Open Scope logic.

Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainP6.

Lemma piece0 : piece6_stmt -> piece0_stmt.
Proof.
  intros H6 Espec gv v1 v2. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call. Intros n.
  forward_call (n, gv).
  Intros vr. destruct vr as [pi bs]. simpl fst in *; simpl snd in *. subst n.
  forward_call (Ews, pi, bs, Zlength bs, gv).
  Intros ps.
  rewrite sublist_same by lia.
  sep_apply (@split_block C.CS tuchar (Zlength bs) (vb bs) pi eq_refl). Intros.
  sep_apply (@split_block C.CS tuchar (Zlength bs) (vb bs) ps eq_refl). Intros.
  forward_call. Intros c.
  forward_call (c, gv).
  Intros vr. destruct vr as [po1 init1]. simpl fst in *; simpl snd in *.
  sep_apply (@split_block C.CS tuint c (vb init1) po1 eq_refl). Intros.
  forward_call (c, gv).
  Intros vr. destruct vr as [po2 init2]. simpl fst in *; simpl snd in *.
  sep_apply (@split_block C.CS tuint c (vb init2) po2 eq_refl). Intros.
  subst c.
  eapply semax_pre; [ | apply (H6 Espec gv v1 v2 bs pi ps init1 po1 init2 po2) ].
  unfold pre6, u32s. entailer!.
Qed.
