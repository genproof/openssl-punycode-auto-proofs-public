(* 32-bit arithmetic facts for ossl_punycode_decode: OpenSSL's division-based overflow tests. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.DecModel.

Lemma repr_nonzero: forall w, 1 <= w <= Int.max_unsigned -> Int.repr w <> Int.zero.
Proof.
  intros w H E. apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by lia.
  rewrite Int.unsigned_zero in E. lia.
Qed.

Lemma unsigned_m1_sub: forall a, 0 <= a <= Int.max_unsigned -> Int.unsigned (Int.repr (-1 - a)) = maxint - a.
Proof.
  intros. rewrite Int.unsigned_repr_eq. change Int.modulus with 4294967296. unfold maxint.
  replace (-1 - a) with ((4294967295 - a) + (-1) * 4294967296) by lia.
  rewrite Z_mod_plus by lia. apply Z.mod_small. rep_lia.
Qed.

Lemma divu_unsigned: forall a w, 0 <= a <= Int.max_unsigned -> 1 <= w <= Int.max_unsigned ->
  Int.unsigned (Int.divu (Int.repr a) (Int.repr w)) = a / w.
Proof.
  intros. unfold Int.divu. rewrite (Int.unsigned_repr a), (Int.unsigned_repr w) by lia. apply Int.unsigned_repr.
  split. apply Z.div_pos; lia. apply Z.le_trans with a; [ | lia]. apply Z.div_le_upper_bound; nia.
Qed.

Lemma divu_m1_sub: forall a w, 0 <= a <= Int.max_unsigned -> 1 <= w <= Int.max_unsigned ->
  Int.unsigned (Int.divu (Int.repr (-1 - a)) (Int.repr w)) = (maxint - a) / w.
Proof.
  intros. unfold Int.divu. rewrite unsigned_m1_sub by lia. rewrite (Int.unsigned_repr w) by lia.
  apply Int.unsigned_repr. unfold maxint in *.
  split. apply Z.div_pos; rep_lia. apply Z.le_trans with (4294967295 - a); [ | rep_lia]. assert (0 <= 4294967295 - a) by rep_lia. apply Z.div_le_upper_bound; nia.
Qed.

Lemma divu_m1: forall w, 1 <= w <= Int.max_unsigned ->
  Int.unsigned (Int.divu (Int.repr (-1)) (Int.repr w)) = maxint / w.
Proof. intros. pose proof (divu_m1_sub 0 w). rewrite Z.sub_0_r in H0. apply H0; rep_lia. Qed.

(* digit > (maxint - i) / w  <->  i + digit * w > maxint *)
Lemma test_digit: forall i d w, 0 <= i <= maxint -> 1 <= w -> 0 <= d ->
  ((maxint - i) / w < d <-> maxint < i + d * w).
Proof. intros. rewrite div_test by lia. lia. Qed.

(* w > maxint / c  <->  w * c > maxint *)
Lemma test_w: forall w c, 1 <= c -> 0 <= w -> (maxint / c < w <-> maxint < w * c).
Proof. intros. rewrite div_test by (unfold maxint; lia). lia. Qed.

(* i / (c + 1) > maxint - n  <->  n + i / (c + 1) > maxint *)
Lemma test_n: forall n q, (maxint - n < q <-> maxint < n + q).
Proof. intros. lia. Qed.
