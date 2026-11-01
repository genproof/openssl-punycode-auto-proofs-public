(* pr_encode: one round of the main loop (code point mm = the minimum code point >= n). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncPass.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.proof.harness.EncMin.
Require Import OpensslPunycode.proof.harness.EncRound2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Lemma cmpu_gt64: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cgt (Int64.repr a) (Int64.repr b)) = Vint (Int.repr (if b <? a then 1 else 0)).
Proof.
  intros. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt b a), (b <? a) eqn:E; try reflexivity; [apply Z.ltb_ge in E | apply Z.ltb_lt in E]; lia.
Qed.

Lemma enc_round: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (B n delta bias h: Z) (out: list Z)
  (f: nat),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap -> 0 <= B <= Int.max_unsigned ->
  encode cps = enc_rounds cps f n delta bias h B out -> Zlength cps - h < Z.of_nat f ->
  h = cnt_lt n cps -> 128 <= n <= maxint + 1 -> 0 <= delta <= maxint + 1 -> 0 <= bias <= 2400 ->
  Zlength out <= ocap -> h < Zlength cps ->
  semax DeltaE
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_round
   (overridePost (enc_inv shc pc cps sho po ocap oinit shl pl B) (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros until f. intros ? ? ? ? ? ? ? ? Hk Hf Hh Hn Hd Hb Ho Hlt.
  destruct f as [|f]; [simpl in Hf; lia|].
  rewrite enc_rounds_step in Hk by lia.
  pose proof (cnt_lt_le n cps) as Hcl.
  assert (Hmx: maxint = Int.max_unsigned) by reflexivity.
  destruct (min_ge_props cps n) as [Hmm [Hin Hmin]]; [rewrite Hmx; auto | apply cnt_lt_exists; lia |].
  set (mm := min_ge cps n) in *.
  pose proof (cnt_eq_In mm cps Hin) as Hce.
  pose proof (Zlength_nonneg out) as Hol.
  subst h. set (h := cnt_lt n cps) in *.
  unfold stmt_round, enc_post. abbreviate_semax.
  forward.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (enc_min shc pc cps sho po ocap oinit shl pl n delta bias h B out); auto; lia ].
    entailer!. }
  unfold stmt_round2. change (min_ge cps n) with mm.
  forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr
      (if orb (maxint <? delta) ((maxint - delta) / (h + 1) <? mm - n) then 1 else 0)));
      temp _mm (Vlong (Int64.repr mm));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl)).
  { forward. entailer!. fix_cmp. replace (maxint <? delta) with true by (unfold maxint in *; lia). reflexivity. }
  { forward.
    { entailer!. change (Int.signed (Int.repr 1)) with 1 in *. repr0_false. }
    entailer!. fix_cmp. replace (maxint <? delta) with false by (unfold maxint in *; lia). rewrite orb_false_l.
    change (Int.signed (Int.repr 1)) with 1.
    unfold maxint in *.
    assert (0 <= (4294967295 - delta) / (h + 1) <= 4294967295)
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
    rewrite ?sub64_repr, ?add64_repr, ?divu_repr64 by rep_lia. rewrite cmpu_gt64 by rep_lia. reflexivity. }
  forward_if.
  { forward. apply ret0_entail; [ | apply bufv_len; lia]. apply encode_fits_none. rewrite Hk.
    destruct (orb (maxint <? delta) ((maxint - delta) / (h + 1) <? mm - n)) eqn:E; [reflexivity |].
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
  eapply semax_pre; [ | apply (enc_round_rest shc pc cps sho po ocap oinit shl pl B n delta bias h out f mm);
    auto; try lia ].
  entailer!.
Qed.
