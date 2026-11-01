(* ossl_a2ulabel, ACE branch, code-point loop body, part A: t'13 = buf[i]; t'7 = codepoint2utf8(seed, t'13);
   utfsize = t'7. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uAceRange.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uAceDefs.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma utf8_len_le4: forall c, 0 <= Zlength (utf8 c) <= 4.
Proof.
  intros c. unfold utf8.
  destruct (c <? 128); [|destruct (c <? 2048); [|destruct (c <? 65536); [|destruct (c <=? 1114111)]]];
  simpl; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma cp_a_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh R,
  a2u_ctx shi pin s sho out cap init -> cps_ok cps bv -> 0 <= i < Zlength cps ->
  semax DeltaA
    (cp_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh)
    s_cpa
    (overridePost (cp_a gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh) R).
Proof.
  intros Espec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh R
    CTX [CF [CL BL]] HI.
  unfold cp_inv, cp_a, s_cpa. abbreviate_semax.
  Intros sv.
  assert (HC: 0 <= Znth i cps <= maxint) by (apply (proj1 (Forall_Znth _ _) CF i HI)).
  assert (HZ: Znth i (vb cps ++ sublist (Zlength cps) 512 bv) = Vint (Int.repr (Znth i cps))).
  { rewrite Znth_app1 by (unfold vb; rewrite Zlength_map; lia). unfold vb. rewrite Znth_map by lia. reflexivity. }
  forward.
  { entailer!. setoid_rewrite HZ. auto. }
  setoid_rewrite HZ.
  forward_call (Tsh, vseed, sv, Znth i cps).
  { entailer!. simpl. unfold maxint in HC. rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { unfold maxint in HC. rep_lia. }
  Intros new.
  pose proof (utf8_len_le4 (Znth i cps)) as HU.
  forward.
  destruct R; cbv beta iota; cbn [tycontext.RA_normal].
  Exists new. entailer!.
Qed.
