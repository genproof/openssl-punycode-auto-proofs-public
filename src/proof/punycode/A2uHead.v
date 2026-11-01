(* ossl_a2ulabel, label loop: FIND (tmpptr = strchr(inptr, '.')), DELTA (its length), CMP (t'9 =
   OPENSSL_strncasecmp(inptr, "xn--", 4)), then any continuation c1; c2. *)
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
Require Import OpensslPunycode.proof.punycode.A2uHeadDelta.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma a2u_head_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed
    st w sh c1 c2 R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  (forall c9, -512 <= c9 <= 512 -> (c9 =? 0) = is_ace (label_of (rest_at s st)) ->
     semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
       (a2u_head gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c9) (Ssequence c1 c2) R) ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (PROP ()
     LOCAL (temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
            lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
            lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
     SEP (a2u_frame gv out cap tk zf live; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr shi pin s st;
          scratch vbuf vbs vseed))
    (Ssequence s_find (Ssequence s_delta (Ssequence (Ssequence s_cmp c1) c2))) R.
Proof.
  intros Espec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c1 c2 R CTX ST HC.
  pose proof CTX as (RS & WS & OK & PIN & FC & CAP & LI & POUT).
  assert (OKr: str_ok (rest_at s st)) by (apply Forall_sublist; exact OK).
  assert (TMP: tmp_at pin s st = if index_of 46 (rest_at s st) <? Zlength (rest_at s st)
                                 then offset_val (index_of 46 (rest_at s st)) (offset_val st pin) else nullval).
  { unfold tmp_at. rewrite offset_offset_val. reflexivity. }
  unfold instr.
  rewrite <- (cstr_piece shi s pin st ST PIN). fold (rest_at s st).
  unfold s_find, s_cmp.
  abbreviate_semax. Intros.
  forward_call (shi, rest_at s st, offset_val st pin, 46).
  rewrite <- TMP.
  apply (a2u_delta_ok Espec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh); auto.
  unfold a2u_frame. rewrite xn_lit_cstr. abbreviate_semax. Intros.
  forward_call (shi, rest_at s st, offset_val st pin, Ers, [120; 110; 45; 45], gv ___stringlit_punycode_1, 4).
  { repeat constructor; rep_lia. }
  assert (BR: bytes_ok (rest_at s st ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact OKr]; simpl; intros; lia | repeat constructor; rep_lia]. }
  assert (BX: bytes_ok ([120; 110; 45; 45] ++ [0])) by (repeat constructor; rep_lia).
  eapply semax_pre; [|apply (HC (ncasecmp (rest_at s st ++ [0]) ([120; 110; 45; 45] ++ [0]) 4))].
  - unfold a2u_head, a2u_frame, instr. rewrite xn_lit_cstr.
    rewrite <- (cstr_piece shi s pin st ST PIN). fold (rest_at s st).
    entailer!.
  - apply ncasecmp_range; auto.
  - apply ace_test; auto.
Qed.
