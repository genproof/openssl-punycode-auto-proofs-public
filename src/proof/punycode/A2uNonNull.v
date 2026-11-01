(* ossl_a2ulabel: the start of the body (inptr = in; result = 1; if (out == NULL) return -1) for out <> NULL, then
   any rest. *)
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

Ltac dead :=
  first [ contradiction | discriminate
        | exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end
        | match goal with H: _ |- _ => solve [inv H] end ].

Lemma a2u_nonnull_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed REST,
  readable_share shi -> writable_share sho -> str_ok s -> 0 <= cap <= Int64.max_unsigned ->
  out <> nullval -> Zlength init = cap -> sizeof tk <= 0 -> shim_bounds fn zf live ->
  (a2u_ctx shi pin s sho out cap init ->
   semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (PROP ()
     LOCAL (temp _result (Vint (Int.repr 1)); temp _inptr pin;
            lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
            lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv;
            temp _out out; temp _outlen (Vlong (Int64.repr cap)))
     SEP (data_at_ Tsh (tarray tuchar 6) vseed; data_at_ Tsh tuint vbs;
          data_at_ Tsh (Tstruct _wpacket_st noattr) vpkt; data_at_ Tsh (tarray tuint 512) vbuf;
          puny_consts gv; xn_lit gv; shim_state gv fn zf live; mem_mgr gv; cstr shi s pin;
          data_at sho (tarray tuchar cap) init out; zero_tok cap tk out))
    REST (a2u_R gv shi pin s sho out cap init tk fn zf live)) ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (PROP ()
     LOCAL (lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
            lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv;
            temp _in pin; temp _out out; temp _outlen (Vlong (Int64.repr cap)))
     SEP (data_at_ Tsh (tarray tuchar 6) vseed; data_at_ Tsh tuint vbs;
          data_at_ Tsh (Tstruct _wpacket_st noattr) vpkt; data_at_ Tsh (tarray tuint 512) vbuf;
          puny_consts gv; xn_lit gv; shim_state gv fn zf live; mem_mgr gv; cstr shi s pin;
          out_buf sho out cap init tk))
    (Ssequence (Sset _inptr (Etempvar _in (tptr tschar)))
      (Ssequence (Sset _result (Econst_int (Int.repr 1) tint)) (Ssequence s_ifout REST)))
    (a2u_R gv shi pin s sho out cap init tk fn zf live).
Proof.
  intros Espec gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed REST SH SH0 H H0 Eo H1 H2 H3 K.
  unfold a2u_R, s_ifout. abbreviate_semax.
  forward. forward.
  assert_PROP (isptr pin /\ field_compatible (tarray tuchar (Zlength s + 1)) [] pin) as PF.
  { unfold cstr. rewrite (data_at_tuchar_cs ShCS CS). entailer!. }
  destruct PF as [Ppin FCs].
  subst cap.
  unfold out_buf at 1. rewrite if_false by auto.
  assert_PROP (isptr out) as Pout by entailer!.
  forward_if.
  { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    unfold zero_tok. destruct (Z.eq_dec (Zlength init) 0) as [Z0|Z0].
    - apply sepcon_valid_pointer2. apply malloc_token_valid_pointer. eapply Z.le_trans; [apply sizeof_sh_le | exact H2].
    - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      apply data_at_valid_ptr; [auto | simpl; rep_lia]. }
  { forward. destruct out; try contradiction. match goal with H: typed_true _ _ |- _ => simpl in H; inv H end. }
  flatten_sepcon_in_SEP.
  try (unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS).
  try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
  eapply semax_pre; [| apply K; exact (conj SH (conj SH0 (conj H (conj Ppin (conj FCs (conj H0 (conj eq_refl Pout))))))) ].
  entailer!.
Qed.
