(* The digit loop of the decoder reads back the digits the encoder writes (RFC 3492 5: generalized variable-length
   integers), without overflow for the deltas of an encoding of at most 512 code points <= 0x10FFFF.
  *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* Every octet of the digits of q (q <= maxint) is a lowercase letter or a decimal digit. *)
Definition enc_digits_chars_stmt : Prop := forall q k bias,
  0 <= q <= maxint ->
  Forall (fun c => (97 <= c <= 122) \/ (48 <= c <= 57)) (enc_digits 64 q k bias).

(* The decoder's digit loop, from the first digit of q with i (and w = 1, k = 36), returns i + q and the position
   after the last digit.  The bound 600000000 > 1114112 * 513 + 512 covers every delta of such an encoding. *)
Definition digits_enc_digits_stmt : Prop := forall pre rest q bias i,
  0 <= q -> 0 <= i -> i + q <= 600000000 ->
  let inp := pre ++ enc_digits 64 q 36 bias ++ rest in
  digits inp (Z.to_nat (Zlength inp - Zlength pre)) (Zlength pre) i 1 36 bias
  = Some (i + q, Zlength pre + Zlength (enc_digits 64 q 36 bias)).

Lemma threshold_range : forall k bias, 1 <= threshold k bias <= 26.
Proof.
  intros; unfold threshold.
  destruct (Z.leb_spec k bias); [lia|].
  destruct (Z.leb_spec (bias + 26) k); lia.
Qed.

Lemma threshold_mono : forall k bias, threshold k bias <= threshold (k + 36) bias.
Proof.
  intros; unfold threshold.
  destruct (Z.leb_spec k bias), (Z.leb_spec (k + 36) bias),
    (Z.leb_spec (bias + 26) k), (Z.leb_spec (bias + 26) (k + 36)); lia.
Qed.

Lemma digit_char_range : forall d, 0 <= d < 36 ->
  (97 <= digit_char d <= 122) \/ (48 <= digit_char d <= 57).
Proof.
  intros; unfold digit_char.
  destruct (Z.ltb_spec d 26); lia.
Qed.

Lemma digit_value_char : forall d, 0 <= d < 36 -> digit_value (digit_char d) = d.
Proof.
  intros; unfold digit_char, digit_value.
  destruct (Z.ltb_spec d 26);
  repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end;
  cbn [andb]; lia.
Qed.

(* One non-final digit: the quotient left is below a tenth of q. *)
Lemma enc_quot_bound : forall q t f, 1 <= t <= 26 -> t <= q < 10 ^ Z.of_nat (S f) ->
  0 <= (q - t) / (36 - t) < 10 ^ Z.of_nat f.
Proof.
  intros q t f Ht Hq.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hq by lia.
  split. { apply Z.div_pos; lia. }
  apply Z.le_lt_trans with ((q - t) / 10).
  - apply Z.div_le_compat_l; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma enc_digits_chars_gen : forall f q k bias, 0 <= q < 10 ^ Z.of_nat f ->
  Forall (fun c => (97 <= c <= 122) \/ (48 <= c <= 57)) (enc_digits f q k bias).
Proof.
  induction f; intros q k bias Hq; cbn [enc_digits].
  - constructor; [apply digit_char_range; simpl in Hq; lia | constructor].
  - pose proof (threshold_range k bias).
    destruct (Z.ltb_spec q (threshold k bias)).
    + constructor; [apply digit_char_range; lia | constructor].
    + constructor.
      * apply digit_char_range.
        assert (0 <= (q - threshold k bias) mod (36 - threshold k bias) < 36 - threshold k bias) by (apply Z.mod_pos_bound; lia). lia.
      * apply IHf. apply enc_quot_bound; lia.
Qed.

Lemma Znth_mid : forall (pre l: list Z) c, Znth (Zlength pre) (pre ++ c :: l) = c.
Proof.
  intros. rewrite app_Znth2 by lia. rewrite Z.sub_diag. apply Znth_0_cons.
Qed.

Lemma pow32_small : forall j w, 0 <= j -> 32 ^ j <= w <= 35 ^ j -> w <= 600000000 -> w * 35 <= maxint.
Proof.
  intros j w Hj Hw Hw6. unfold maxint.
  destruct (Z_lt_le_dec j 6).
  - assert (35 ^ j <= 35 ^ 5) by (apply Z.pow_le_mono_r; lia).
    change (35 ^ 5) with 52521875 in H. lia.
  - assert (32 ^ 6 <= 32 ^ j) by (apply Z.pow_le_mono_r; lia).
    change (32 ^ 6) with 1073741824 in H. lia.
Qed.

Lemma digits_gen : forall f q k bias pre rest i w n,
  0 <= q < 10 ^ Z.of_nat f -> 0 <= i -> 1 <= w -> i + q * w <= 600000000 ->
  (threshold k bias <= 4 -> exists j, 0 <= j /\ 32 ^ j <= w <= 35 ^ j) ->
  (length (enc_digits f q k bias) <= n)%nat ->
  digits (pre ++ enc_digits f q k bias ++ rest) n (Zlength pre) i w k bias
  = Some (i + q * w, Zlength pre + Zlength (enc_digits f q k bias)).
Proof.
  induction f; intros q k bias pre rest i w n Hq Hi Hw Hiq Hinv Hn.
  - simpl in Hq. assert (q = 0) by lia. subst q.
    destruct n as [|n]; [simpl in Hn; lia|].
    pose proof (threshold_range k bias).
    cbn [enc_digits digits app].
    rewrite Znth_mid, digit_value_char by lia.
    rewrite Zlength_app, Zlength_cons.
    pose proof (Zlength_nonneg rest).
    destruct (Z.leb_spec (Zlength pre + Z.succ (Zlength rest)) (Zlength pre)); [lia|].
    destruct (Z.leb_spec 36 0); [lia|].
    destruct (Z.ltb_spec maxint (i + 0 * w)); [unfold maxint in *; lia|].
    destruct (Z.ltb_spec 0 (threshold k bias)); [|lia].
    rewrite Zlength_cons, Zlength_nil; try (f_equal; f_equal; lia).
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
      assert (0 <= q * w) by (apply Z.mul_nonneg_nonneg; lia).
      destruct (Z.ltb_spec maxint (i + q * w)); [unfold maxint in *; lia|].
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
      destruct (Z.ltb_spec maxint (i + (t + r) * w)); [unfold maxint in *; lia|].
      fold t.
      destruct (Z.ltb_spec (t + r) t); [lia|].
      assert (Hw1 : w * (36 - t) <= maxint).
      { assert (Htw : t * w <= q * w) by (apply Z.mul_le_mono_nonneg_r; lia).
        assert (Hwq : w <= q * w) by (rewrite <- (Z.mul_1_l w) at 1; apply Z.mul_le_mono_nonneg_r; lia).
        assert (w * (36 - t) = 36 * w - t * w) by ring.
        destruct (Z_lt_le_dec t 5).
        - destruct (Hinv ltac:(lia)) as [j [Hj Hjw]].
          assert (w * 35 <= maxint) by (apply (pow32_small j); lia).
          assert (w * 1 <= w * t) by (apply Z.mul_le_mono_nonneg_l; lia).
          unfold maxint in *. lia.
        - assert (w * 5 <= w * t) by (apply Z.mul_le_mono_nonneg_l; lia).
          unfold maxint. lia. }
      destruct (Z.ltb_spec maxint (w * (36 - t))); [lia|].
      replace (pre ++ digit_char (t + r) :: e' ++ rest) with ((pre ++ [digit_char (t + r)]) ++ e' ++ rest)
        by (rewrite <- app_assoc; reflexivity).
      replace (Zlength pre + 1) with (Zlength (pre ++ [digit_char (t + r)]))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      unfold e'. rewrite IHf.
      * rewrite Zlength_app, Zlength_cons, Zlength_cons, Zlength_nil. f_equal. f_equal; lia.
      * exact Hq'.
      * lia.
      * lia.
      * lia.
      * intros Ht'.
        assert (Ht4 : t <= 4) by (pose proof (threshold_mono k bias); unfold t; lia).
        destruct (Hinv Ht4) as [j [Hj Hjw]].
        exists (j + 1). split; [lia|].
        rewrite !Z.pow_add_r, !Z.pow_1_r by lia.
        pose proof (Z.pow_nonneg 32 j ltac:(lia)).
        split; apply Z.mul_le_mono_nonneg; lia.
      * cbn [enc_digits] in Hn. fold t in Hn. destruct (Z.ltb_spec q t); [lia|]. cbn [length] in Hn. fold q' in Hn. lia.
Qed.

Theorem rt_digits : enc_digits_chars_stmt /\ digits_enc_digits_stmt.
Proof.
  split.
  - intros q k bias Hq. apply enc_digits_chars_gen.
    unfold maxint in Hq. split; [lia|].
    eapply Z.le_lt_trans; [apply Hq|]. reflexivity.
  - intros pre rest q bias i Hq Hi Hiq inp. subst inp.
    pose proof (digits_gen 64 q 36 bias pre rest i 1
      (Z.to_nat (Zlength (pre ++ enc_digits 64 q 36 bias ++ rest) - Zlength pre))) as H.
    rewrite Z.mul_1_r in H. apply H; try lia.
    + intros _. exists 0. rewrite !Z.pow_0_r. lia.
    + rewrite !Zlength_app. pose proof (Zlength_nonneg rest).
      rewrite (Zlength_correct (enc_digits 64 q 36 bias)). lia.
Qed.

Definition enc_digits_chars : enc_digits_chars_stmt := proj1 rt_digits.
Definition digits_enc_digits : digits_enc_digits_stmt := proj2 rt_digits.
