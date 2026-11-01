(* encode: one round of the main loop (the minimum code point >= n, the overflow test, the pass, delta++). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require OpensslPunycode.proof.harness.EncRound.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncModel.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncMin.
Local Open Scope logic.

Local Opaque enc_digits adapt.

(* UINT64_MAX as the constant of the code (-1) and as Int64.max_unsigned. *)
Lemma u64max_repr: Int64.repr (-1) = Int64.repr Int64.max_unsigned.
Proof. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma tenc_round: tpass_ok -> tround_ok.
Proof.
  intros Hpass. unfold tround_ok.
  intros until f. intros ? ? ? Hcf ? ? ? ? Hk Hf Hh Hn Hd Hb Ho Hlt.
  destruct f as [|f]; [simpl in Hf; lia|].
  pose proof (cnt_lt_le n cps) as Hcl.
  rewrite enc_rounds_step in Hk by lia.
  assert (Hmx: maxint = Int.max_unsigned) by reflexivity.
  assert (Hcf': Forall (fun c => 0 <= c <= maxint) cps) by (rewrite Hmx; auto).
  assert (Hex := cnt_lt_exists n cps ltac:(lia)).
  destruct (min_ge_props cps n Hcf' Hex) as [Hmm [Hin Hmin]].
  pose proof (min_ge_u64 cps n Hcf' Hex) as Hu.
  set (mm := min_ge cps n) in *.
  pose proof (cnt_eq_In mm cps Hin) as Hce.
  pose proof (Zlength_nonneg out) as Hol.
  subst h. set (h := cnt_lt n cps) in *.
  rewrite tstmt_roundbody_eq. unfold tpost. abbreviate_semax.
  forward.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (tenc_min shc pc cps sho po room oinit shl pl n delta bias h B out); auto; lia ].
    rewrite u64max_repr. entailer!. }
  rewrite Hu. unfold tstmt_round2. abbreviate_semax.
  forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr
      (if orb (maxint <? delta) ((maxint - delta) / (h + 1) <? mm - n) then 1 else 0)));
      temp _min (Vlong (Int64.repr mm));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
  { change (Int.unsigned (Int.repr (-1))) with maxint in *.
    forward. entailer!. fix_cmp. replace (maxint <? delta) with true by (unfold maxint in *; lia). reflexivity. }
  { change (Int.unsigned (Int.repr (-1))) with maxint in *.
    forward.
    { entailer!. change (Int.signed (Int.repr 1)) with 1 in *. repr0_false. }
    entailer!. fix_cmp. replace (maxint <? delta) with false by (unfold maxint in *; lia). rewrite orb_false_l.
    change (Int.signed (Int.repr 1)) with 1.
    unfold maxint in *.
    assert (0 <= (4294967295 - delta) / (h + 1) <= 4294967295)
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
    change (Int.unsigned (Int.repr (-1))) with 4294967295.
    rewrite ?sub64_repr, ?add64_repr, ?divu_repr64 by rep_lia. rewrite EncRound.cmpu_gt64 by rep_lia.
    reflexivity. }
  forward_if.
  { forward. apply tret0_entail; [ | apply bufv_len; lia]. apply encode_fits_none. rewrite Hk.
    match goal with |- (if ?b then _ else _) = _ => destruct b eqn:E; [reflexivity |] end.
    exfalso. match goal with H: (if _ then 1 else 0) <> 0 |- _ => apply H end.
    unfold Z.div in E. rewrite E. reflexivity. }
  match goal with H: Int.repr (if _ then 1 else 0) = Int.zero |- _ => rename H into Ht2 end.
  change (let (q, _) := Z.div_eucl (maxint - delta) (h + 1) in q) with ((maxint - delta) / (h + 1)) in Ht2.
  destruct (orb (maxint <? delta) ((maxint - delta) / (h + 1) <? mm - n)) eqn:Ec.
  { exfalso. apply (f_equal Int.unsigned) in Ht2.
    rewrite Int.unsigned_repr in Ht2 by rep_lia. rewrite Int.unsigned_zero in Ht2. lia. }
  apply orb_false_iff in Ec. destruct Ec as [Ec1 Ec2]. apply Z.ltb_ge in Ec1. apply Z.ltb_ge in Ec2.
  assert (Hmul: (mm - n) * (h + 1) <= maxint - delta).
  { eapply Z.le_trans; [apply Z.mul_le_mono_nonneg_r; [lia | exact Ec2] |].
    rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
  assert (Hmul0: 0 <= (mm - n) * (h + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  forward. forward.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (Hpass Espec shc pc cps sho po room oinit shl pl f mm h B
        (delta + (mm - n) * (h + 1)) bias out); auto; try lia ].
    entailer!. }
  Intros delta' bias' h' out'.
  pose proof (cnt_round n mm cps ltac:(lia) Hmin) as Hcr.
  rewrite Nat2Z.inj_succ in Hf.
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  forward.
  unfold tenc_cont. Exists mm (delta' + 1) bias' h' out' f. entailer!.
Qed.
