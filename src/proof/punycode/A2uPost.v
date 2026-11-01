(* ossl_a2ulabel: after the label loop (s_post): the final NUL, WPACKET_cleanup, the return. *)
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

(* The outcome of a successful conversion is that of a2u_labels. *)
Lemma a2u_outcome_labels: forall out cap s init zf,
  out <> nullval -> cap <> 0 ->
  a2u_outcome out cap s init 0 zf false =
    (fst (a2u_labels cap ([], false) (labels s)), 0, zf,
     vb (fst (snd (a2u_labels cap ([], false) (labels s)))) ++
       sublist (Zlength (fst (snd (a2u_labels cap ([], false) (labels s))))) cap init).
Proof.
  intros. unfold a2u_outcome, a2ulabel. rewrite if_false by auto. replace (cap =? 0) with false by lia. simpl.
  destruct (a2u_labels cap ([], false) (labels s)) as [r [w sh]]. reflexivity.
Qed.

(* The final NUL of a2u_cont at the end of the string. *)
Lemma a2u_cont_nil: forall cap w sh,
  a2u_cont cap (w, sh) [] =
    (if PacketSpec.put_ok cap w [0] then res_of sh else 0, (fst (put cap (w, false) [0]), orb sh (negb (PacketSpec.put_ok cap w [0])))).
Proof.
  intros. unfold a2u_cont, put, PacketSpec.put_ok, res_of. simpl. change (Zlength [0]) with 1.
  destruct (cap - Zlength w <? 1) eqn:E; simpl.
  - replace (1 <=? cap - Zlength w) with false by lia. simpl. rewrite orb_true_r. auto.
  - replace (1 <=? cap - Zlength w) with true by lia. simpl. rewrite orb_false_r. auto.
Qed.

Lemma instr_cstr: forall shi pin s st,
  0 <= st <= Zlength s -> isptr pin -> field_compatible (tarray tuchar (Zlength s + 1)) [] pin ->
  instr shi pin s st = cstr shi s pin.
Proof.
  intros. unfold instr.
  rewrite <- (piece_split shi (s ++ [0]) (Zlength s + 1) pin 0 st (Zlength s + 1))
    by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; auto; lia).
  rewrite <- cstr_piece by (auto; pose proof (Zlength_nonneg s); lia).
  rewrite sublist_same by lia. rewrite isptr_offset_val_zero by auto. reflexivity.
Qed.

Lemma scratch_data_at_: forall vbuf vbs vseed,
  scratch vbuf vbs vseed |--
  data_at_ Tsh (tarray tuchar 6) vseed * data_at_ Tsh tuint vbs * data_at_ Tsh (tarray tuint 512) vbuf.
Proof.
  intros. unfold scratch. Intros bv bsv sv.
  sep_apply (data_at_data_at_ Tsh (tarray tuint 512) bv vbuf).
  sep_apply (data_at_data_at_ Tsh tuint bsv vbs).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 6) sv vseed).
  cancel.
Qed.

(* The record after WPACKET_cleanup, any contents, as forward_call's change_compspecs would otherwise convert it
   (a conversion the kernel checks by unfolding both composite environments). *)
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

Ltac dead :=
  first [ contradiction | discriminate
        | exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end
        | match goal with H: _ |- _ => solve [inv H] end ].

Lemma a2u_post_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed,
  a2u_ctx shi pin s sho out cap init -> out <> nullval -> 0 < cap -> shim_bounds 0 zf (live + 1) ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (a2u_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed)
    s_post
    (a2u_R gv shi pin s sho out cap init tk 0 zf live).
Proof.
  intros Espec gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed CTX Eo CP HB.
  destruct CTX as [SHI [SHO [STR [PP [FC [CAPR [LEN PO]]]]]]].
  unfold a2u_brk, s_post, a2u_R. abbreviate_semax.
  Intros st w sh r.
  unfold a2u_frame. Intros.
  rewrite (instr_cstr shi pin s st) by auto. sep_apply (scratch_data_at_ vbuf vbs vseed).
  destruct H0 as [[-> E] | [-> E]].
  - Intros. apply -> seq_assoc. apply semax_if_seq. forward_if. { dead. } forward. apply semax_if_seq.
    forward_if. { dead. }
    forward_call (gv, Tsh, vpkt, sho, out, cap, init, w, sub, 0, zf, live + 1).
    replace (live + 1 - 1) with live by lia. forward. Exists false.
    rewrite a2u_outcome_labels by (auto; lia). rewrite E. simpl. unfold out_buf; rewrite if_false by auto. entailer!.
  - rewrite a2u_cont_nil in E.
    assert (R1: (if sh then 0 else 1) <> -1) by (destruct sh; lia).
    assert (R2: Int.repr (if sh then 0 else 1) <> Int.repr (-1)) by (destruct sh; intro X; inv X).
    set (r := if sh then 0 else 1) in *.
    destruct (PacketSpec.put_ok cap w [0]) eqn:EP.
    + Intros. apply -> seq_assoc. apply semax_if_seq. forward_if; [|dead].
      forward_call (Tsh, vpkt, sho, out, cap, init, w, sub, 0). rewrite EP. forward.
      apply semax_if_seq. forward_if; [dead|].
      forward_call (gv, Tsh, vpkt, sho, out, cap, init, fst (put cap (w, false) [0]), sub, 0, zf, live + 1).
      replace (live + 1 - 1) with live by lia. forward. Exists false.
      rewrite a2u_outcome_labels by (auto; lia). rewrite E. simpl. unfold out_buf; rewrite if_false by auto. entailer!.
    + Intros. apply -> seq_assoc. apply semax_if_seq. forward_if; [|dead].
      forward_call (Tsh, vpkt, sho, out, cap, init, w, sub, 0). rewrite EP. forward.
      apply semax_if_seq. forward_if; [|dead]. forward.
      forward_call (gv, Tsh, vpkt, sho, out, cap, init, fst (put cap (w, false) [0]), sub, 0, zf, live + 1).
      replace (live + 1 - 1) with live by lia. forward. Exists false.
      rewrite a2u_outcome_labels by (auto; lia). rewrite E. simpl. unfold out_buf; rewrite if_false by auto. entailer!.
Qed.
