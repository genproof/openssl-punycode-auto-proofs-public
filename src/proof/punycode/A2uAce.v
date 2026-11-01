(* ossl_a2ulabel, label loop: an A-label is decoded (ossl_punycode_decode into buf) and its code points written
   in UTF-8 (codepoint2utf8 into seed, WPACKET_memcpy); break with result -1 when it does not decode or a code point
   is above 0x10FFFF. *)
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
Require Import OpensslPunycode.proof.punycode.A2uAceDefs.
Require Import OpensslPunycode.proof.punycode.A2uAceDec.
Require Import OpensslPunycode.proof.punycode.A2uAceLoop.
Require Import OpensslPunycode.proof.punycode.A2uAceCp.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma a2u_ace_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed
    st w sh c9 R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  a2u_labels cap ([], false) (labels s) = a2u_labels cap (w, sh) (labels (rest_at s st)) ->
  is_ace (label_of (rest_at s st)) = true ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (a2u_head gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c9)
    s_ace
    (overridePost (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st)
       (a2u_loopR gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R)).
Proof.
  intros until R. intros CTX Hst H1 HA.
  pose proof (a2u_labels_first cap (w, sh) (rest_at s st)) as M. rewrite <- H1 in M.
  rewrite s_ace_eq. eapply ace_dec_ok; eauto. intros cps bv OK LS.
  apply semax_seq with (cp_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv); [apply ace_loop_ok; auto; intros; apply cp_body_ok; auto|].
  unfold cp_brk, s_fin. abbreviate_semax.
  Intros w' sh' r sv.
  rewrite LS in M. destruct OK as (OK1 & OK2 & OK3).
  assert (LB: Zlength (vb cps ++ sublist (Zlength cps) 512 bv) = 512).
  { rewrite Zlength_app, Zlength_vb, Zlength_sublist by (pose proof (Zlength_nonneg cps); lia). lia. }
  destruct H as [[-> E]|[-> E]]; rewrite E in M.
  - forward_if.
    + forward.
      unfold a2u_loopR, loop1_ret_assert, overridePost; destruct R; cbv beta iota; cbn [tycontext.RA_break tycontext.RA_normal].
      unfold a2u_brk. Exists st w' sh' (-1).
      unfold scratch. Exists (vb cps ++ sublist (Zlength cps) 512 bv) (Vint (Int.repr (Zlength cps))) sv.
      entailer!. unfold a2u_end. auto.
    + exfalso. apply H; reflexivity.
  - forward_if.
    + exfalso. unfold res_of in *. destruct sh'; simpl in *; discriminate.
    + forward.
      unfold a2u_loopR, loop1_ret_assert, overridePost; destruct R; cbv beta iota; cbn [tycontext.RA_break tycontext.RA_normal].
      unfold a2u_lab. Exists w' sh'.
      unfold scratch. Exists (vb cps ++ sublist (Zlength cps) 512 bv) (Vint (Int.repr (Zlength cps))) sv.
      entailer!.
Qed.
