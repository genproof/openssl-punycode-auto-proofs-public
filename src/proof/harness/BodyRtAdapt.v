(* The body of pr_adapt: its loop against adapt_loop, by the fuel left (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

Lemma adapt_loop_fuel: forall f g d k,
  0 <= d < 455 * 35 ^ Z.of_nat f -> (f <= g)%nat -> adapt_loop f d k = adapt_loop g d k.
Proof.
  induction f; intros g d k Hd Hfg.
  - simpl in Hd. destruct g; simpl; auto. rewrite (proj2 (Z.ltb_ge _ _)) by lia. auto.
  - destruct g; [lia|]. simpl. destruct (455 <? d) eqn:E; auto. apply IHf; [|lia].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hd by lia.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma body_pr_adapt' : semax_body Vprog Gprog_none f_pr_adapt pr_adapt_spec.
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
  forward_if (PROP () LOCAL (temp _k (Vlong (Int64.repr 0)); temp _delta (Vlong (Int64.repr d0));
     temp _numpoints (Vlong (Int64.repr numpoints))) SEP ()).
  { forward. entailer!. subst d0. rewrite (proj2 (Z.eqb_neq _ _)) by auto. unfold Int64.divu.
    rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia). auto. }
  { forward. entailer!. subst d0. assert (firsttime = 0). { apply repr_inj_signed; auto; rep_lia. }
    subst. simpl. unfold Int64.divu. rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia). auto. }
  assert (Em: maxint / 2 = 2147483647) by reflexivity. rewrite Em in Hd0.
  assert (Hq: 0 <= d0 / numpoints <= d0).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
  assert (HR: R = adapt_loop 7 d1 0).
  { assert (E7: 455 * 35 ^ Z.of_nat 7 > 4294967296) by reflexivity.
    subst R d1 d0. unfold adapt. destruct (firsttime =? 0); simpl negb; cbv iota;
      (symmetry; apply adapt_loop_fuel; [ lia | lia ]). }
  forward.
  { entailer!. apply (f_equal Int64.unsigned) in H2.
    rewrite Int64.unsigned_repr in H2 by rep_lia. rewrite Int64.unsigned_zero in H2. lia. }
  assert (Hd1: Int64.add (Int64.repr d0) (Int64.divu (Int64.repr d0) (Int64.repr numpoints)) = Int64.repr d1).
  { unfold Int64.divu. rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia).
    rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia. auto. }
  rewrite Hd1.
  forward_while (EX j: nat, EX d: Z,
    PROP (0 <= d < 455 * 35 ^ Z.of_nat j; d <= maxint; (j <= 7)%nat; adapt_loop j d (36 * (7 - Z.of_nat j)) = R)
    LOCAL (temp _k (Vlong (Int64.repr (36 * (7 - Z.of_nat j)))); temp _delta (Vlong (Int64.repr d))) SEP ()).
  { Exists 7%nat d1. entailer!. unfold maxint; lia. }
  { entailer!. }
  { unfold maxint in *. change ((36 - 1) * 26 / 2) with 455 in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
    destruct j as [|j]; [simpl in H2; lia|].
    forward. forward.
    Exists (j, d / 35). entailer!.
    rewrite Nat2Z.inj_succ in *.
    split; [|split; [|split; [|split]]].
    - rewrite Z.pow_succ_r in H2 by lia.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    - apply Z.div_le_upper_bound; lia.
    - lia.
    - simpl in H5. rewrite (proj2 (Z.ltb_lt _ _)) in H5 by lia. rewrite <- H5. f_equal. lia.
    - f_equal. f_equal. lia. }
  unfold maxint in *. change ((36 - 1) * 26 / 2) with 455 in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
  forward.
  { entailer!. apply (f_equal Int64.unsigned) in H6.
    rewrite Int64.unsigned_repr in H6 by rep_lia. rewrite Int64.unsigned_zero in H6. lia. }
  entailer!. rewrite <- H5. replace (36 - 1 + 1) with 36 by lia.
  destruct j; simpl; [|rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity.
Qed.
