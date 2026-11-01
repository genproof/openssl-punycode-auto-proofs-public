(* Piece 4 of the main of harness/api_decode_deterministic.c: cap = nondet_u32(), out1 and out2 = any_uints(cap)
   (DdetMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetMainDefs.
Local Open Scope logic.

Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

Lemma piece4 : piece7_stmt -> piece4_stmt.
Proof.
  intros H7 Espec gv v1 v2 bs len pf ps. unfold pre4, T4, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward_call tt.
  Intros c.
  forward_call (c, gv).
  Intros vret. destruct vret as [po1 vs1]. simpl fst in *. simpl snd in *.
  forward_call (c, gv).
  Intros vret. destruct vret as [po2 vs2]. simpl fst in *. simpl snd in *.
  rewrite !(@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuint c)) by reflexivity.
  rewrite !(data_at_tuint_cs CM.CS CS).
  eapply semax_pre; [ | apply (H7 Espec gv v1 v2 bs len pf ps c vs1 vs2 po1 po2) ].
  unfold pre7, mblock_ui. entailer!.
Qed.
