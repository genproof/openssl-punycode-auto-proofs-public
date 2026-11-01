(* ossl_a2ulabel: one iteration of the label loop (s_label), from its invariant: A2uHead, then A2uNonAce or
   A2uAce, then A2uTail. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uModel.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uHead.
Require Import OpensslPunycode.proof.punycode.A2uNonAce.
Require Import OpensslPunycode.proof.punycode.A2uAce.
Require Import OpensslPunycode.proof.punycode.A2uTail.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma a2u_label_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R,
  a2u_ctx shi pin s sho out cap init ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (a2u_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed)
    s_label
    (a2u_loopR gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R).
Proof.
  intros. unfold a2u_inv. Intros st w sh.
  rewrite s_label_eq. apply -> semax_skip_seq.
  eapply a2u_head_ok; eauto. intros c9 Hc9 Hace.
  apply semax_seq with (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st).
  2: apply a2u_tail_ok; auto.
  unfold a2u_head at 1.
  destruct (is_ace (label_of (rest_at s st))) eqn:EA.
  - try rewrite EA in Hace. apply Z.eqb_eq in Hace. subst c9.
    forward_if.
    + exfalso. match goal with H: context [Int.eq] |- _ => rewrite Int.eq_true in H; discriminate end.
    + eapply semax_pre; [| apply a2u_ace_ok; eauto]. unfold a2u_head. entailer!.
  - try rewrite EA in Hace. apply Z.eqb_neq in Hace.
    forward_if.
    + eapply semax_pre; [| apply a2u_nonace_ok; eauto]. unfold a2u_head. entailer!.
    + exfalso. match goal with H: context [Int.eq] |- _ =>
        rewrite Int.eq_false in H; [apply H; reflexivity | intro E; apply repr_inj_signed in E; [lia | rep_lia | rep_lia]] end.
Qed.
