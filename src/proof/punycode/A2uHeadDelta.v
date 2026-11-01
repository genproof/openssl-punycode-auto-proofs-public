(* ossl_a2ulabel, label loop: DELTA (delta = tmpptr != NULL ? tmpptr - inptr : strlen(inptr)), then any
   continuation c.  Used by A2uHead. *)
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
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
(* strchr's result is a valid pointer into the string. *)
Lemma cstr_valid_at: forall sh s pin st j,
  readable_share sh -> field_compatible (tarray tuchar (Zlength s + 1)) [] pin -> isptr pin ->
  0 <= st <= Zlength s -> 0 <= j <= Zlength s - st ->
  cstr sh (sublist st (Zlength s) s) (offset_val st pin) |-- valid_pointer (offset_val (st + j) pin).
Proof.
  intros sh s pin st j RS FC PIN ST J.
  rewrite cstr_piece by auto.
  rewrite (piece_split sh (s ++ [0]) (Zlength s + 1) pin st (st + j) (Zlength s + 1)) by
    (auto; try lia; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  apply sepcon_valid_pointer2. unfold piece. apply data_at_valid_ptr.
  - apply readable_nonidentity; auto.
  - simpl. rewrite Z.max_r by lia. lia.
Qed.

(* tmpptr - inptr *)
Lemma ptr_sub_off: forall b i a j, 0 <= j <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tschar) (tptr tschar) (offset_val (a + j) (Vptr b i))
    (offset_val a (Vptr b i))) = Vlong (Int64.repr j).
Proof.
  intros b i a j J. simpl.
  unfold sem_sub_pp. rewrite peq_true. simpl. rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted.
  rewrite Ptrofs.divs_one by (compute; congruence). unfold Vptrofs. simpl.
  replace (Ptrofs.sub (Ptrofs.repr (a + j)) (Ptrofs.repr a)) with (Ptrofs.repr j).
  - unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by lia. reflexivity.
  - unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr. replace j with ((a + j) - a) at 1 by lia.
    apply Ptrofs.eqm_sub; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma a2u_delta_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed
    st w sh c R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (PROP ()
     LOCAL (temp _delta (Vlong (Int64.repr (index_of 46 (rest_at s st)))); temp _tmpptr (tmp_at pin s st);
            temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
            lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
            lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
     SEP (cstr shi (rest_at s st) (offset_val st pin); a2u_frame gv out cap tk zf live;
          PacketSpec.wpkt Tsh vpkt sho out cap init w sub; piece shi (s ++ [0]) 0 st pin; scratch vbuf vbs vseed))
    c R ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (PROP ()
     LOCAL (temp _tmpptr (tmp_at pin s st);
            temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
            lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
            lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
     SEP (cstr shi (rest_at s st) (offset_val st pin); a2u_frame gv out cap tk zf live;
          PacketSpec.wpkt Tsh vpkt sho out cap init w sub; piece shi (s ++ [0]) 0 st pin; scratch vbuf vbs vseed))
    (Ssequence s_delta c) R.
Proof.
  intros Espec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c R CTX ST HC.
  destruct CTX as (RS & WS & OK & PIN & FC & CAP & LI & POUT).
  assert (OKr: str_ok (rest_at s st)) by (apply Forall_sublist; exact OK).
  set (rest := rest_at s st) in *.
  set (j := index_of 46 rest) in *.
  assert (TMP: tmp_at pin s st = if j <? Zlength rest then offset_val j (offset_val st pin) else nullval).
  { unfold tmp_at. fold rest. fold j. rewrite offset_offset_val. reflexivity. }
  assert (LR: Zlength rest = Zlength s - st) by (unfold rest, rest_at; rewrite Zlength_sublist; lia).
  assert (SZ: Zlength s <= Ptrofs.max_unsigned).
  { destruct FC as (_ & _ & SZ & _). destruct pin; try contradiction. unfold size_compatible in SZ.
    simpl sizeof in SZ. pose proof (Ptrofs.unsigned_range i). rewrite Z.max_r in SZ by lia.
    unfold Ptrofs.max_unsigned. lia. }
  pose proof (index_of_range 46 rest) as JR. fold j in JR.
  unfold s_delta.
  abbreviate_semax.
  forward_if (PROP ()
    LOCAL (temp _t'3 (Vlong (Int64.repr j)); temp _tmpptr (tmp_at pin s st); temp _inptr (offset_val st pin);
           temp _result (Vint (Int.repr (res_of sh)));
           lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
           lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
    SEP (cstr shi rest (offset_val st pin); a2u_frame gv out cap tk zf live;
         PacketSpec.wpkt Tsh vpkt sho out cap init w sub; piece shi (s ++ [0]) 0 st pin; scratch vbuf vbs vseed)).
  - rewrite TMP. destruct (j <? Zlength rest) eqn:E.
    + apply Z.ltb_lt in E. rewrite offset_offset_val.
      apply denote_tc_test_eq_split; [|apply valid_pointer_zero64; reflexivity].
      repeat apply sepcon_valid_pointer1.
      apply cstr_valid_at; auto. lia.
    + simpl. entailer!.
  - rewrite TMP in *. destruct (j <? Zlength rest) eqn:E; [|contradiction H; reflexivity].
    apply Z.ltb_lt in E. rewrite offset_offset_val in *. destruct pin; try contradiction.
    forward.
    + entailer!. unfold sameblock. destruct (peq b b); [reflexivity|congruence].
    + rewrite ptr_sub_off by lia. destruct R; cbv beta iota. cbn [tycontext.RA_normal]. rewrite TMP. apply ENTAIL_refl.
  - rewrite TMP in *. destruct (j <? Zlength rest) eqn:E.
    { rewrite offset_offset_val in H. destruct pin; try contradiction; discriminate. }
    apply Z.ltb_ge in E. assert (JE: j = Zlength rest) by lia.
    forward_call (shi, rest, offset_val st pin).
    forward.
    destruct R; cbv beta iota. cbn [tycontext.RA_normal]. rewrite TMP, JE. entailer!.
  - forward.
    eapply semax_pre; [|exact HC]. entailer!.
Qed.
