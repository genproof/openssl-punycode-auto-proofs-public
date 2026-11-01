(* ossl_a2ulabel: WPACKET_init_static_len and its test (s_init), up to the label loop. *)
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

Lemma a2u_outcome_fail: forall out cap s init fn zf live sub fn' zf' live',
  out <> nullval -> cap <> 0 -> zalloc_outcome PacketSpec.sub_size fn zf live sub fn' zf' live' -> sub = nullval ->
  a2u_outcome out cap s init fn zf true = (-1, fn', zf', init) /\ live' = live.
Proof.
  intros. subst sub. unfold zalloc_outcome in H1. unfold a2u_outcome.
  rewrite if_false by auto. replace (cap =? 0) with false by lia.
  rewrite if_false in H1 by (unfold PacketSpec.sub_size; lia).
  destruct (Z.eq_dec fn 0).
  - subst fn. simpl. destruct H1 as [-> [[_ [-> ->]] | [N _]]]; [auto | contradiction].
  - replace (fn =? 0) with false by lia. simpl. destruct H1 as [_ [-> [-> ->]]]. auto.
Qed.

Lemma a2u_outcome_ok: forall out cap s init fn zf live sub fn' zf' live',
  out <> nullval -> cap <> 0 -> zalloc_outcome PacketSpec.sub_size fn zf live sub fn' zf' live' -> sub <> nullval ->
  a2u_outcome out cap s init fn zf false =
    (fst (a2ulabel s cap), 0, zf, vb (snd (a2ulabel s cap)) ++ sublist (Zlength (snd (a2ulabel s cap))) cap init)
  /\ fn' = 0 /\ zf' = zf /\ live' = live + 1 /\ fn = 0.
Proof.
  intros. unfold zalloc_outcome in H1. unfold a2u_outcome.
  rewrite if_false by auto. replace (cap =? 0) with false by lia.
  rewrite if_false in H1 by (unfold PacketSpec.sub_size; lia).
  destruct (Z.eq_dec fn 0).
  - subst fn. simpl. destruct H1 as [-> [[N _] | [_ [-> ->]]]]; [contradiction|].
    destruct (a2ulabel s cap); auto.
  - destruct H1 as [N _]; contradiction.
Qed.

Ltac dead :=
  first [ contradiction | discriminate
        | exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end
        | match goal with H: _ |- _ => solve [inv H] end ].

Ltac dead_if := match goal with H: typed_true _ _ |- _ => simpl in H; inv H
                                 | H: typed_false _ _ |- _ => simpl in H; inv H end.

Lemma cstr_instr0: forall shi pin s, isptr pin ->
  cstr shi s pin = instr shi pin s 0.
Proof.
  intros. unfold instr. rewrite piece_empty by (rewrite isptr_offset_val_zero; auto).
  rewrite emp_sepcon. rewrite <- cstr_piece by (auto; pose proof (Zlength_nonneg s); lia).
  rewrite sublist_same by lia. rewrite isptr_offset_val_zero by auto. reflexivity.
Qed.

Lemma scratch_init: forall vbuf vbs vseed,
  data_at_ Tsh (tarray tuchar 6) vseed * data_at_ Tsh tuint vbs * data_at_ Tsh (tarray tuint 512) vbuf
  |-- scratch vbuf vbs vseed.
Proof.
  intros. unfold scratch, data_at_.
  Exists (default_val (tarray tuint 512)) (default_val tuint) (default_val (tarray tuchar 6)).
  entailer!.
Qed.

(* The record of a failed init, any contents, as forward_call's change_compspecs would otherwise convert it (by a
   conversion the kernel checks by unfolding both composite environments: minutes at Qed). *)
Lemma exp_pkt_cs: forall sh p,
  (EX v: @reptype PkCS OpensslPunycode.proof.packet.PacketSpec.t_pkt,
     @data_at PkCS sh OpensslPunycode.proof.packet.PacketSpec.t_pkt v p) =
  @data_at_ CS sh (Tstruct _wpacket_st noattr) p.
Proof.
  intros. rewrite pkt_to_packet. apply pred_ext.
  - Intros v. apply data_at_data_at_.
  - rewrite data_at__eq. Exists (@default_val PkCS OpensslPunycode.proof.packet.PacketSpec.t_pkt). apply derives_refl.
Qed.

Local Ltac change_compspecs' cs cs' ::=
  first [ rewrite exp_pkt_cs
        | match goal with
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | reflexivity]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | reflexivity]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| reflexivity]
  | |- context [@malloc_token cs' ?sh ?t] => erewrite (@malloc_token_change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
     end ].

Lemma a2u_init_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed,
  a2u_ctx shi pin s sho out cap init -> out <> nullval -> sizeof tk <= 0 -> shim_bounds fn zf live ->
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
    s_init
    (overridePost
       (EX sub: val, !! (fn = 0 /\ 0 < cap) && a2u_inv gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed)
       (a2u_R gv shi pin s sho out cap init tk fn zf live)).
Proof.
  intros Espec gv shi pin s sho out cap init tk fn zf live vbuf vpkt vbs vseed CTX Eo H1 HB.
  destruct CTX as [SHI [SHO [STR [PP [FC [CAPR [LEN PO]]]]]]]. subst cap.
  unfold s_init, a2u_R. abbreviate_semax.
  rewrite pkt_to_packet, (data_at_tuchar_cs CS PkCS sho).
  forward_call (gv, Tsh, vpkt, sho, out, Zlength init, init, fn, zf, live, tk).
  Intros vret. destruct vret as [[[[r sub] fn'] zf'] live']. simpl fst in *; simpl snd in *.
  match goal with H: if Z.eq_dec _ 0 then _ else _ |- _ => rename H into HZ end.
  destruct (Z.eq_dec (Zlength init) 0) as [C0|C0].
  { destruct HZ as [-> [-> [-> [-> ->]]]]. rewrite if_true by auto.
    forward_if.
    - forward. Exists false. unfold a2u_outcome, out_buf. rewrite !if_false by auto.
      replace (Zlength init =? 0) with true by lia. simpl.
      entailer!. all: try apply derives_refl.
    - dead. }
  destruct HZ as [ZO Er].
  destruct (eq_dec sub nullval) as [Sn|Sn].
  { subst r. rewrite if_true by auto.
    destruct (a2u_outcome_fail out (Zlength init) s init fn zf live sub fn' zf' live' Eo C0 ZO Sn) as [Eq ->].
    forward_if.
    - forward. Exists true. rewrite Eq. unfold out_buf. rewrite !if_false by auto. simpl.
      entailer!. all: try apply derives_refl.
    - dead. }
  subst r. rewrite if_false by (intro; discriminate).
  destruct (a2u_outcome_ok out (Zlength init) s init fn zf live sub fn' zf' live' Eo C0 ZO Sn) as [Eq [-> [-> [-> ->]]]].
  forward_if.
  { dead. }
  forward.
  rewrite (cstr_instr0 shi pin s) by auto. sep_apply (scratch_init vbuf vbs vseed).
  Exists sub. unfold a2u_inv. Exists 0 (@nil Z) false.
  unfold rest_at, res_of. rewrite sublist_same by lia. rewrite isptr_offset_val_zero by auto.
  unfold a2u_frame. entailer!.
Qed.
