(* ossl_a2ulabel, ACE branch: the body of the code-point loop (s_cpbody) at i < bufsize. *)
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
Require Import OpensslPunycode.proof.punycode.A2uAceCpA.
Require Import OpensslPunycode.proof.punycode.A2uAceCpB.
Require Import OpensslPunycode.proof.punycode.A2uAceCpC.
Lemma cp_body_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh R,
  a2u_ctx shi pin s sho out cap init -> cps_ok cps bv -> 0 <= i < Zlength cps ->
  semax DeltaA
    (cp_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh)
    s_cpbody
    (loop1_ret_assert (cp_mid gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i) (overridePost (cp_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv) R)).
Proof.
  intros. rewrite s_cpbody_eq.
  apply semax_seq with (cp_a gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh); [apply cp_a_ok; auto|].
  apply semax_seq with (cp_b gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh); [apply cp_b_ok; auto|].
  match goal with |- semax _ _ _ ?Q =>
    replace Q with (overridePost (cp_mid gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i) Q) by (destruct R; reflexivity) end.
  apply cp_cd_ok; auto.
Qed.
