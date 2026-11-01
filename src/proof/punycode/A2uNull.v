(* ossl_a2ulabel: the start of the body (inptr = in; result = 1; if (out == NULL) return -1), then any rest. *)
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

Lemma a2u_null_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed REST,
  readable_share shi -> writable_share sho -> str_ok s -> 0 <= cap <= Int64.max_unsigned ->
  out = nullval -> sizeof tk <= 0 -> shim_bounds fn zf live ->
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
  intros Espec gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed REST SH SH0 H H0 Eo H2 H3.
  unfold a2u_R, s_ifout. abbreviate_semax.
  forward. forward.
  subst out. unfold out_buf at 1. rewrite if_true by auto.
    forward_if.
    - forward. Exists true. unfold a2u_outcome, out_buf. rewrite !if_true by auto. entailer!. apply derives_refl.
    - dead.
Qed.
