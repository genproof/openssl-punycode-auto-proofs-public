(* The body of the harness's RFC 3492 encoder encode (harness/rt_roundtrip.c) against TrtSpec.encode_spec: the copy
   of the basic code points, the delimiter, then the main loop (TrtEncMain.v), whose rounds (TrtEncRound.v), passes
   (TrtEncPass.v) and digits (TrtEncDig.v) are proved in their own files. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncBasic.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncMain.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncRound.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncPass.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDig.
Local Open Scope logic.

Lemma RA_normal_for: forall I R, RA_normal (for_ret_assert I R) = I.
Proof. intros I R; destruct R; reflexivity. Qed.

(* The pieces composed: the digits in the pass, the pass in the round. *)
Lemma tenc_round_ok: tround_ok.
Proof. apply tenc_round, tenc_pass, tenc_dig. Qed.

Lemma body_encode : semax_body Vprog Gprog_encode f_encode encode_spec.
Proof.
start_function.
forward. forward. forward. forward. forward.
forward_for_simple_bound (Zlength cps) (EX j: Z,
  PROP (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) <= room)
  LOCAL (temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar room (bufv (filter (fun c => c <? 128) (sublist 0 j cps)) room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps))))) pl)).
{ entailer!.
  - rewrite sublist_nil. simpl. rewrite Zlength_nil. lia.
  - unfold bufv. rewrite sublist_nil. simpl filter. unfold vb; simpl map.
    rewrite Zlength_nil, sublist_same by lia. simpl app. auto. }
{ rename i into j.
  eapply semax_pre; [ | eapply semax_post; [ | | | | apply (tenc_basic_body shc pc cps sho po room oinit shl pl j); auto ] ].
  { unfold tbasic_st. entailer!. }
  { rewrite RA_normal_oP. unfold POSTCONDITION, abbreviate. rewrite RA_normal_for. apply ENTAIL_refl. }
  { apply brk_enc. }
  { apply cont_enc. }
  { intros. apply ENTAIL_refl. } }
rewrite sublist_same by lia.
Intros.
assert (HB: 0 <= Zlength (filter (fun c => c <? 128) cps) <= Zlength cps)
  by (split; [apply Zlength_nonneg | apply (cnt_lt_le 128 cps)]).
set (bs := filter (fun c => c <? 128) cps) in *.
(* The delimiter: written when b > 0; encode returns 0 when it does not fit. *)
destruct (0 <? Zlength bs) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
- destruct (Zlength bs <? room) eqn:Er; [apply Z.ltb_lt in Er | apply Z.ltb_ge in Er].
  + forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr 0)); temp _b (Vlong (Int64.repr (Zlength bs)));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv (bs ++ [45]) room oinit) po;
           data_at shl tulong (Vlong (Int64.repr (Zlength (bs ++ [45])))) pl)).
    { forward_call (sho, po, room, bufv bs room oinit, shl, pl, Zlength bs, 45).
      { apply bufv_len; lia. }
      replace (Zlength bs <? room) with true by lia.
      forward. rewrite bufv_upd by lia. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!. }
    { fix_cmp. lia. }
    forward_if. { contradiction. }
    unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
    eapply semax_pre; [ | apply (tenc_main tenc_round_ok shc pc cps sho po room oinit shl pl (Zlength bs) (bs ++ [45]));
      auto; [ replace (0 <? Zlength bs) with true by lia; reflexivity
            | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ] ].
    entailer!.
  + forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr 1)))
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv bs room oinit) po;
           data_at shl tulong (Vlong (Int64.repr (Zlength bs))) pl)).
    { forward_call (sho, po, room, bufv bs room oinit, shl, pl, Zlength bs, 45).
      { apply bufv_len; lia. }
      replace (Zlength bs <? room) with false by lia.
      forward. entailer!. }
    { fix_cmp. lia. }
    forward_if. 2: { discriminate. }
    forward.
    eapply derives_trans; [ | apply (tret0_entail cps _ oinit shc pc sho po shl pl (bufv bs (Zlength oinit) oinit)
      (Vlong (Int64.repr (Zlength bs)))) ]; [cancel | | apply bufv_len; lia].
    apply encode_fits_delim; fold bs; lia.
- forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr 0)); temp _b (Vlong (Int64.repr (Zlength bs)));
       temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
       temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
       temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv bs room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength bs))) pl)).
  { fix_cmp. lia. }
  { forward. entailer!. }
  forward_if. { contradiction. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (tenc_main tenc_round_ok shc pc cps sho po room oinit shl pl (Zlength bs) bs);
    auto; replace (0 <? Zlength bs) with false by lia; reflexivity ].
  entailer!.
Qed.
