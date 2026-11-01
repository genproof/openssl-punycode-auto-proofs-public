(* The digit loop of the decoder reads back the digits the encoder writes (RFC 3492 5: generalized variable-length
   integers), for any delta q <= maxint and any start i: it returns i + q when that sum fits in maxint, and fails
   otherwise.  This is RtDigits.digits_enc_digits without its bound on i + q; it holds for every bias the encoder
   uses (at most 215, the largest value adapt gives for a delta <= maxint). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.RtDigits.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The bias: adapt of a delta <= maxint is at most 215                     *)
(* ---------------------------------------------------------------------- *)

Lemma adapt_loop_end : forall d k, 0 <= d -> k + (36 * d) / (d + 38) <= k + 35.
Proof.
  intros d k Hd.
  assert ((36 * d) / (d + 38) < 36) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* Each division by 35 of the loop adds 36; m divisions bring any d < 456 * 35^m to at most 455. *)
Lemma adapt_loop_bound : forall m f d k, 0 <= d < 456 * 35 ^ Z.of_nat m -> (m <= f)%nat ->
  adapt_loop f d k <= k + 36 * Z.of_nat m + 35.
Proof.
  induction m as [|m IH]; intros f d k Hd Hf.
  - simpl in Hd. destruct f as [|f]; cbn [adapt_loop].
    + pose proof (adapt_loop_end d k). lia.
    + destruct (Z.ltb_spec 455 d); [lia|]. pose proof (adapt_loop_end d k). lia.
  - destruct f as [|f]; [lia|]. cbn [adapt_loop].
    destruct (Z.ltb_spec 455 d).
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hd by lia.
      assert (0 <= d / 35 < 456 * 35 ^ Z.of_nat m).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
      specialize (IH f (d / 35) (k + 36) H0 ltac:(lia)). lia.
    + pose proof (adapt_loop_end d k). lia.
Qed.

Lemma adapt_bound : forall delta np ft, 0 <= delta <= maxint -> 1 <= np -> adapt delta np ft <= 215.
Proof.
  intros delta np ft Hd Hnp. unfold adapt.
  set (d0 := if ft then delta / 700 else delta / 2).
  assert (0 <= d0 <= delta / 2).
  { subst d0; destruct ft; split; try (apply Z.div_pos; lia).
    - apply Z.div_le_compat_l; lia.
    - lia. }
  assert (0 <= d0 / np <= d0).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
  assert (delta / 2 * 2 <= delta) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  pose proof (adapt_loop_bound 5 64 (d0 + d0 / np) 0) as Hl.
  simpl Z.of_nat in Hl. change (456 * 35 ^ 5) with 23949975000 in Hl. unfold maxint in Hd.
  specialize (Hl ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The digit loop                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma threshold_small : forall k bias, threshold k bias < 18 -> k < bias + 18.
Proof.
  intros k bias; unfold threshold.
  destruct (Z.leb_spec k bias); [lia|].
  destruct (Z.leb_spec (bias + 26) k); lia.
Qed.

(* From digit j (k = 36 (j + 1), weight w <= 35^j) with i: the loop gives i + q w when it fits, else fails.  The
   weight check never fails before: a non-final digit has t w <= q w <= maxint, so w (36 - t) <= maxint when
   t >= 18, and t < 18 needs k < bias + 18 <= 233, i.e. j <= 5 and w (36 - t) <= 35^6. *)
Lemma digits_gen_any : forall f q k bias pre rest i w n j,
  0 <= q < 10 ^ Z.of_nat f -> 0 <= i -> 1 <= w -> bias <= 215 ->
  0 <= j -> k = 36 * (j + 1) -> w <= 35 ^ j ->
  (length (enc_digits f q k bias) <= n)%nat ->
  digits (pre ++ enc_digits f q k bias ++ rest) n (Zlength pre) i w k bias
  = if i + q * w <=? maxint then Some (i + q * w, Zlength pre + Zlength (enc_digits f q k bias)) else None.
Proof.
  induction f; intros q k bias pre rest i w n j Hq Hi Hw Hbias Hj Hk Hwj Hn.
  - simpl in Hq. assert (q = 0) by lia. subst q.
    destruct n as [|n]; [simpl in Hn; lia|].
    pose proof (threshold_range k bias).
    cbn [enc_digits digits app].
    rewrite Znth_mid, digit_value_char by lia.
    rewrite Zlength_app, Zlength_cons.
    pose proof (Zlength_nonneg rest).
    destruct (Z.leb_spec (Zlength pre + Z.succ (Zlength rest)) (Zlength pre)); [lia|].
    destruct (Z.leb_spec 36 0); [lia|].
    destruct (Z.ltb_spec maxint (i + 0 * w)), (Z.leb_spec (i + 0 * w) maxint); try lia; auto.
    destruct (Z.ltb_spec 0 (threshold k bias)); [|lia].
    rewrite Zlength_cons, Zlength_nil; reflexivity.
  - pose proof (threshold_range k bias) as Ht.
    destruct n as [|n].
    { simpl in Hn. destruct (q <? threshold k bias); simpl in Hn; lia. }
    cbn [enc_digits].
    destruct (Z.ltb_spec q (threshold k bias)).
    + cbn [digits app].
      rewrite Znth_mid, digit_value_char by lia.
      rewrite Zlength_app, Zlength_cons.
      pose proof (Zlength_nonneg rest).
      destruct (Z.leb_spec (Zlength pre + Z.succ (Zlength rest)) (Zlength pre)); [lia|].
      destruct (Z.leb_spec 36 q); [lia|].
      destruct (Z.ltb_spec maxint (i + q * w)), (Z.leb_spec (i + q * w) maxint); try lia; auto.
      destruct (Z.ltb_spec q (threshold k bias)); [|lia].
      rewrite Zlength_cons, Zlength_nil. reflexivity.
    + set (t := threshold k bias) in *.
      set (r := (q - t) mod (36 - t)).
      set (q' := (q - t) / (36 - t)).
      assert (Hdiv : q - t = (36 - t) * q' + r) by (apply Z.div_mod; lia).
      assert (Hr : 0 <= r < 36 - t) by (apply Z.mod_pos_bound; lia).
      assert (Hq' : 0 <= q' < 10 ^ Z.of_nat f) by (apply enc_quot_bound; lia).
      set (e' := enc_digits f q' (k + 36) bias).
      cbn [digits app].
      rewrite Znth_mid, digit_value_char by lia.
      rewrite Zlength_app, Zlength_cons.
      pose proof (Zlength_nonneg rest). pose proof (Zlength_nonneg e').
      destruct (Z.leb_spec (Zlength pre + Z.succ (Zlength (e' ++ rest))) (Zlength pre));
        [rewrite Zlength_app in *; lia|].
      destruct (Z.leb_spec 36 (t + r)); [lia|].
      assert (Hqw : q * w = (t + r) * w + q' * (w * (36 - t)))
        by (replace q with (t + r + (36 - t) * q') at 1 by lia; ring).
      assert (Hw36 : 1 <= w * (36 - t)) by (replace 1 with (1 * 1) by reflexivity;
        apply Z.mul_le_mono_nonneg; lia).
      assert (0 <= q' * (w * (36 - t))) by (apply Z.mul_nonneg_nonneg; lia).
      assert (Htrw : 0 <= (t + r) * w) by (apply Z.mul_nonneg_nonneg; lia).
      destruct (Z.ltb_spec maxint (i + (t + r) * w)).
      { destruct (Z.leb_spec (i + q * w) maxint); [lia|reflexivity]. }
      fold t.
      destruct (Z.ltb_spec (t + r) t); [lia|].
      assert (Hw1 : i + q * w <= maxint -> w * (36 - t) <= maxint).
      { intros Hiq.
        assert (Htw : t * w <= q * w) by (apply Z.mul_le_mono_nonneg_r; lia).
        destruct (Z_lt_le_dec t 18).
        - apply threshold_small in l. fold t in l.
          assert (j <= 5) by lia.
          assert (35 ^ j <= 35 ^ 5) by (apply Z.pow_le_mono_r; lia).
          change (35 ^ 5) with 52521875 in H5.
          assert (w * (36 - t) <= w * 35) by (apply Z.mul_le_mono_nonneg_l; lia).
          unfold maxint. lia.
        - assert (w * (36 - t) <= w * t) by (apply Z.mul_le_mono_nonneg_l; lia).
          lia. }
      destruct (Z.ltb_spec maxint (w * (36 - t))).
      { destruct (Z.leb_spec (i + q * w) maxint); [specialize (Hw1 ltac:(assumption)); lia|reflexivity]. }
      replace (pre ++ digit_char (t + r) :: e' ++ rest) with ((pre ++ [digit_char (t + r)]) ++ e' ++ rest)
        by (rewrite <- app_assoc; reflexivity).
      replace (Zlength pre + 1) with (Zlength (pre ++ [digit_char (t + r)]))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      unfold e'. rewrite (IHf q' (k + 36) bias _ rest (i + (t + r) * w) (w * (36 - t)) n (j + 1)).
      * replace (i + (t + r) * w + q' * (w * (36 - t))) with (i + q * w) by lia.
        destruct (i + q * w <=? maxint); auto.
        rewrite Zlength_app, Zlength_cons, Zlength_cons, Zlength_nil. f_equal. f_equal; lia.
      * exact Hq'.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * rewrite Z.pow_add_r, Z.pow_1_r by lia.
        apply Z.mul_le_mono_nonneg; lia.
      * cbn [enc_digits] in Hn. fold t in Hn. destruct (Z.ltb_spec q t); [lia|]. cbn [length] in Hn. fold q' in Hn. lia.
Qed.

(* The decoder's digit loop, from the first digit of q with i (and w = 1, k = 36): i + q and the position after
   the last digit when i + q <= maxint, a failure otherwise. *)
Lemma digits_enc_digits_any : forall pre rest q bias i,
  0 <= q <= maxint -> 0 <= i -> bias <= 215 ->
  let inp := pre ++ enc_digits 64 q 36 bias ++ rest in
  digits inp (Z.to_nat (Zlength inp - Zlength pre)) (Zlength pre) i 1 36 bias
  = if i + q <=? maxint then Some (i + q, Zlength pre + Zlength (enc_digits 64 q 36 bias)) else None.
Proof.
  intros pre rest q bias i Hq Hi Hb inp. subst inp.
  rewrite (digits_gen_any 64 q 36 bias pre rest i 1 _ 0).
  - rewrite Z.mul_1_r. reflexivity.
  - unfold maxint in Hq. split; [lia|]. eapply Z.le_lt_trans; [apply Hq|]. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Z.pow_0_r. lia.
  - rewrite !Zlength_app. pose proof (Zlength_nonneg rest).
    rewrite (Zlength_correct (enc_digits 64 q 36 bias)). lia.
Qed.
