(* Piece 0 of the main of harness/api_decode_deterministic.c: len and more drawn, first = any_bytes(len + more),
   second = copy_of(first, len): a copy of the first len octets (DdetMainDefs). *)
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

Lemma piece0 : piece4_stmt -> piece0_stmt.
Proof.
  intros H4 Espec gv v1 v2. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (9223372036854775807).
  Intros len.
  forward_call (9223372036854775807 - len).
  Intros more.
  assert_PROP (len + more <= Int64.max_unsigned) by entailer!.
  forward_call (len + more, gv).
  Intros vret. destruct vret as [pf bs]. simpl fst in *. simpl snd in *.
  rewrite <- H2.
  forward_call (Ews, pf, bs, len, gv).
  Intros ps.
  rewrite !(@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuchar _)) by reflexivity.
  rewrite !(data_at_tuchar_cs CM.CS CS).
  eapply semax_pre; [ | apply (H4 Espec gv v1 v2 bs len pf ps) ].
  unfold pre4, mblock_uc. entailer!.
Qed.
