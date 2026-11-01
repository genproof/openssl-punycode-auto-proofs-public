(* The bodies of the harness's small functions of law rt_roundtrip (harness/rt_roundtrip.c): rfc_adapt (RFC 3492
   6.1, Model.adapt), digit (Model.digit_char) and put (one octet into the output, if there is room). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.BodyRtAdapt.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.

Lemma body_rfc_adapt : semax_body Vprog Gprog_none f_rfc_adapt rfc_adapt_spec.
Proof.
  start_function.
  set (d0 := if firsttime =? 0 then delta / 2 else delta / 700).
  set (d1 := d0 + d0 / numpoints).
  set (R := adapt delta numpoints (negb (firsttime =? 0))).
  assert (Hd0: 0 <= d0 <= maxint / 2).
  { subst d0. destruct (firsttime =? 0); split; try (apply Z.div_pos; lia).
    apply Z.div_le_mono; unfold maxint in *; lia.
    apply Z.le_trans with (delta / 2); [apply Z.div_le_compat_l; lia|].
    apply Z.div_le_mono; unfold maxint in *; lia. }
  forward.
  forward_if (PROP () LOCAL (temp _k (Vlong (Int64.repr 0)); temp _t'1 (Vlong (Int64.repr d0));
     temp _numpoints (Vlong (Int64.repr numpoints))) SEP ()).
  { forward. entailer!. subst d0. rewrite (proj2 (Z.eqb_neq _ _)) by auto. unfold Int64.divu.
    rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia). auto. }
  { forward. entailer!. subst d0. assert (firsttime = 0). { apply repr_inj_signed; auto; rep_lia. }
    subst. simpl. unfold Int64.divu. rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia). auto. }
  forward.
  assert (Em: maxint / 2 = 2147483647) by reflexivity. rewrite Em in Hd0.
  assert (Hq: 0 <= d0 / numpoints <= d0).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
  assert (HR: R = adapt_loop 7 d1 0).
  { assert (E7: 455 * 35 ^ Z.of_nat 7 > 4294967296) by reflexivity.
    subst R d1 d0. unfold adapt. destruct (firsttime =? 0); simpl negb; cbv iota;
      (symmetry; apply OpensslPunycode.proof.harness.BodyRtAdapt.adapt_loop_fuel; [ lia | lia ]). }
  forward.
  { entailer!. apply (f_equal Int64.unsigned) in H2.
    rewrite Int64.unsigned_repr in H2 by rep_lia. rewrite Int64.unsigned_zero in H2. lia. }
  assert (Hd1: Int64.add (Int64.repr d0) (Int64.divu (Int64.repr d0) (Int64.repr numpoints)) = Int64.repr d1).
  { unfold Int64.divu. rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia).
    rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia. auto. }
  rewrite Hd1.
  forward_loop (EX j: nat, EX d: Z,
    PROP ((0 <= d < 455 * 35 ^ Z.of_nat j)%Z; d <= maxint; (j <= 7)%nat; (adapt_loop j d (36 * (7 - Z.of_nat j)) = R)%Z)
    LOCAL (temp _k (Vlong (Int64.repr (36 * (7 - Z.of_nat j))%Z)); temp _delta (Vlong (Int64.repr d))) SEP ())
    continue: (EX j: nat, EX d: Z,
    PROP ((0 <= d < 455 * 35 ^ Z.of_nat j)%Z; d <= maxint; (j < 7)%nat;
          (adapt_loop j d (36 * (7 - Z.of_nat j)) = R)%Z)
    LOCAL (temp _k (Vlong (Int64.repr (36 * (7 - Z.of_nat j) - 36)%Z)); temp _delta (Vlong (Int64.repr d))) SEP ())
    break: (EX d: Z, EX k: Z,
    PROP (d <= 455; 0 <= d; (0 <= k <= 36 * 7)%Z; (k + 36 * d / (d + 38) = R)%Z)
    LOCAL (temp _k (Vlong (Int64.repr k)); temp _delta (Vlong (Int64.repr d))) SEP ()).
  { Exists 7%nat d1. entailer!. unfold maxint; lia. }
  { Intros j d. unfold maxint in *.
    forward_if.
    { rewrite !Int64.unsigned_repr in H6 by rep_lia.
      destruct j as [|j]; [simpl in H2; lia|].
      forward.
      Exists j (d / 35). entailer!.
      rewrite Nat2Z.inj_succ in *.
      split; [|split; [|split]].
      - rewrite Z.pow_succ_r in H2 by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
      - apply Z.div_le_upper_bound; lia.
      - simpl in H5. rewrite (proj2 (Z.ltb_lt _ _)) in H5 by lia. rewrite <- H5. f_equal. lia.
      - f_equal. f_equal. lia. }
    { rewrite !Int64.unsigned_repr in H6 by rep_lia.
      forward. Exists d (36 * (7 - Z.of_nat j)). entailer!.
      rewrite <- H5. destruct j; simpl; [|rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity. } }
  { Intros j d. forward. Exists j d. entailer!.
    f_equal. f_equal. lia. }
  Intros d k. unfold maxint in *.
  forward.
  { entailer!. match goal with Hz: Int64.repr _ = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
      rewrite Int64.unsigned_zero in Hz; lia end. }
Qed.

Lemma body_digit : semax_body Vprog Gprog_none f_digit digit_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vlong (Int64.repr (digit_char d)))) SEP ()).
  { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. entailer!. unfold digit_char.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. auto. }
  { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. entailer!. unfold digit_char.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    do 2 f_equal. lia. }
  forward.
Qed.

Lemma body_put : semax_body Vprog Gprog_none f_put put_spec.
Proof.
  start_function.
  forward.
  forward_if.
  { forward.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. entailer!. }
  assert (Hlt: l <? room = true) by (apply Z.ltb_lt; lia).
  unfold arr0. destruct (Z.eq_dec room 0); [lia|].
  forward. forward. forward. forward. forward.
  rewrite Hlt. entailer!.
  unfold arr0. destruct (Z.eq_dec (Zlength buf) 0); [lia|].
  apply derives_refl'. f_equal. f_equal. f_equal.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  rewrite !zero_ext_inrange; auto; rewrite ?zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia.
Qed.
