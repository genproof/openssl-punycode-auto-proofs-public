(* ossl_a2ulabel, ACE branch: the code-point loop: i = 0; for (; i < bufsize; i++) CPBODY. *)
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
Lemma ace_loop_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv R,
  a2u_ctx shi pin s sho out cap init -> cps_ok cps bv ->
  (* the body (A2uAceCp.cp_body_ok) *)
  (forall i w' sh' R', 0 <= i < Zlength cps ->
     semax DeltaA (cp_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv i w' sh') s_cpbody
       (loop1_ret_assert (cp_mid gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv i) (overridePost (cp_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv) R'))) ->
  semax DeltaA
    (ace_dec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv)
    (Ssequence s_i0 (Sloop (Ssequence s_itest s_cpbody) s_incr))
    (overridePost (cp_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv) R).
Proof.
  intros. destruct H0 as (Hcr & Hcl & Hbl).
  unfold s_i0, s_itest, s_incr. unfold ace_dec. abbreviate_semax.
  forward.
  apply semax_pre with (EX i: Z, EX w': list Z, EX sh': bool, cp_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv i w' sh').
  { Exists 0 w sh. unfold cp_inv. entailer!. rewrite sublist_same by lia. auto. }
  apply semax_loop with (EX i: Z, cp_mid gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv i).
  - Intros i w' sh'. assert_PROP (0 <= i) as Hi0 by (unfold cp_inv; entailer!).
    apply semax_seq with (!! (i < Zlength cps) && cp_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv i w' sh').
    + unfold cp_inv. Intros. forward.
      forward_if.
      * unfold loop1_ret_assert; destruct R; cbv beta iota; cbn [tycontext.RA_normal]. forward. entailer!.
      * unfold loop1_ret_assert; destruct R; cbv beta iota. forward.
        assert (i = Zlength cps) by lia. subst i. rewrite sublist_nil in H2.
        unfold cp_brk. Exists w' sh' (res_of sh'). entailer!.
    + apply semax_extract_prop; intros Hi.
      eapply semax_post; [| | | | apply (H1 i w' sh' R); lia].
      all: unfold abbreviate in POSTCONDITION; subst POSTCONDITION; unfold loop1_ret_assert, overridePost; destruct R;
        cbn [tycontext.RA_normal tycontext.RA_break tycontext.RA_continue tycontext.RA_return];
        try (intros vl; match type of vl with option val => idtac end);
        apply andp_left2; first [apply derives_refl | Exists i; apply derives_refl].
  - Intros i. unfold cp_mid. Intros w' sh'. forward. Exists (i+1) w' sh'. unfold cp_inv. entailer!.
Qed.
