(* ossl_a2ulabel, ACE branch: bufsize = 512; t'6 = ossl_punycode_decode(inptr + 4, delta - 4, buf, &bufsize);
   if (t'6 <= 0) { result = -1; break; }, then any continuation c (CPS) from the decoded code points. *)
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
Require Import OpensslPunycode.proof.punycode.A2uAceDecM.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma ace_dec_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c9 c R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  a2u_labels cap ([], false) (labels s) = a2u_labels cap (w, sh) (labels (rest_at s st)) ->
  is_ace (label_of (rest_at s st)) = true ->
  (forall cps bv, cps_ok cps bv -> label_step cap (w, sh) (label_of (rest_at s st)) = put_utf8s cap (w, sh) cps ->
     semax DeltaA (ace_dec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh cps bv) c
       (overridePost (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st) (a2u_loopR gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R))) ->
  semax DeltaA
    (a2u_head gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c9)
    (Ssequence s_bs (Ssequence (Ssequence s_dec s_dtest) c))
    (overridePost (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st) (a2u_loopR gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R)).
Proof.
  intros until R. intros CTX Hst H1 HA HC.
  pose proof CTX as (Hshi & Hsho & OK & Hpin & FC & Hcap & Hinit & Hout).
  destruct (ace_idx s st Hst HA) as [J1 [J2 JA]].
  assert (LI: Zlength (ace_in (rest_at s st)) = index_of 46 (rest_at s st) - 4).
  { rewrite JA, Zlength_sublist; rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia. }
  assert (OKi: bytes_ok (ace_in (rest_at s st))).
  { unfold ace_in, rest_at. apply Forall_sublist, Forall_sublist.
    eapply Forall_impl; [|exact OK]. simpl; intros; lia. }
  assert (PE: piece shi (s ++ [0]) (st + 4) (st + index_of 46 (rest_at s st)) pin =
     arr0 shi tuchar (Zlength (ace_in (rest_at s st))) (vb (ace_in (rest_at s st))) (offset_val (st + 4) pin)).
  { unfold piece. rewrite <- JA, LI. replace (st + index_of 46 (rest_at s st) - (st + 4)) with (index_of 46 (rest_at s st) - 4) by lia.
    apply data_at_arr0; auto. intros E. rewrite <- LI in E. apply Zlength_nil_inv in E. rewrite E. reflexivity. }
  assert (SP: instr shi pin s st = piece shi (s ++ [0]) 0 st pin * piece shi (s ++ [0]) st (st + 4) pin *
     piece shi (s ++ [0]) (st + 4) (st + index_of 46 (rest_at s st)) pin *
     piece shi (s ++ [0]) (st + index_of 46 (rest_at s st)) (Zlength s + 1) pin).
  { unfold instr. rewrite (piece_split shi (s ++ [0]) (Zlength s + 1) pin st (st + 4) (Zlength s + 1)),
      (piece_split shi (s ++ [0]) (Zlength s + 1) pin (st + 4) (st + index_of 46 (rest_at s st)) (Zlength s + 1));
      rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try lia; auto.
    rewrite !sepcon_assoc. reflexivity. }
  assert (AB: forall bv, data_at Tsh (tarray tuint 512) bv vbuf = arr0 Tsh tuint 512 bv vbuf)
    by (intros; unfold arr0; destruct (Z.eq_dec 512 0); [lia|reflexivity]).
  unfold a2u_head, scratch, a2u_frame, s_bs, s_dec, s_dtest. abbreviate_semax.
  Intros bv bsv sv.
  forward.
  rewrite SP, PE, AB. Intros.
  forward_call (gv, shi, offset_val (st + 4) pin, ace_in (rest_at s st), Tsh, vbuf, 512, bv, Tsh, vbs).
  { entailer!. rewrite LI. reflexivity. }
  { assert (LS: Zlength s + 1 <= Ptrofs.modulus).
    { destruct pin; try contradiction. destruct FC as [_ [_ [SZ _]]]. unfold size_compatible in SZ.
      simpl sizeof in SZ. pose proof (Ptrofs.unsigned_range i). lia. }
    rewrite LI. rep_lia. }
  rewrite <- PE, <- AB.
  destruct (ace_dec_cases s st cap w sh bv OK Hst HA H) as [[arr [E [L LS]]] | [cps [E [OKc LS]]]];
    rewrite E; cbn [fst snd].
  - forward_if.
    + forward. forward.
      unfold a2u_loopR, loop1_ret_assert, overridePost; destruct R; cbv beta iota;
        cbn [tycontext.RA_break tycontext.RA_normal].
      unfold a2u_brk. Exists st w sh (-1). unfold scratch, a2u_frame. Exists arr (Vint (Int.repr 512)) sv.
      rewrite SP. entailer!.
      left. split; auto. rewrite H1, a2u_labels_first, LS. reflexivity.
    + discriminate.
  - forward_if.
    + discriminate.
    + unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
      eapply semax_pre; [|apply (HC cps bv OKc LS)].
      unfold ace_dec, a2u_frame. rewrite SP. Exists sv. entailer!.
Qed.
