(* The body of the harness's function utf8 (harness/rfc_a2ulabel_utf8.c) against its specification
   (Ru8Prog.utf8_spec): for a code point c <= 0x10FFFF it writes Model.utf8 c and returns its length. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.

(* The C operators of utf8 on unsigned int, as arithmetic on Z: a right shift by k is a division by 2^k,
   [& 63] is [mod 64], and [|] of a marker t (whose low j bits are zero) with a value below 2^j is an addition. *)
Lemma ru8_lor_plus: forall j m t x, m = 2 ^ j -> 0 <= j -> t mod m = 0 -> 0 <= x < m -> Z.lor t x = t + x.
Proof.
  intros j m t x -> Hj Ht Hx.
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor; auto.
  - apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
    destruct (Z_lt_le_dec n 0) as [Hn | Hn]; [rewrite Z.testbit_neg_r by lia; auto |].
    destruct (Z_lt_le_dec n j) as [Hnj | Hnj].
    + replace t with ((t / 2 ^ j) * 2 ^ j) by (rewrite (Z.div_mod t (2 ^ j)) at 2 by lia; lia).
      rewrite Z.mul_pow2_bits_low by lia. auto.
    + rewrite <- (Z.mod_small x (2 ^ j)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
  - apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
    destruct (Z_lt_le_dec n 0) as [Hn | Hn]; [rewrite Z.testbit_neg_r by lia; auto |].
    destruct (Z_lt_le_dec n j) as [Hnj | Hnj].
    + replace t with ((t / 2 ^ j) * 2 ^ j) by (rewrite (Z.div_mod t (2 ^ j)) at 2 by lia; lia).
      rewrite Z.mul_pow2_bits_low by lia. auto.
    + rewrite <- (Z.mod_small x (2 ^ j)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma ru8_or_plus: forall j m t x, m = 2 ^ j -> 0 <= j -> 0 <= t -> t mod m = 0 -> 0 <= x < m ->
  t + x <= Int.max_unsigned -> Int.or (Int.repr t) (Int.repr x) = Int.repr (t + x).
Proof.
  intros. unfold Int.or. rewrite !Int.unsigned_repr by lia. f_equal. eapply ru8_lor_plus; eauto.
Qed.

Lemma ru8_shru_div: forall k m c, m = 2 ^ k -> 0 <= k < 32 -> 0 <= c <= Int.max_unsigned ->
  Int.shru (Int.repr c) (Int.repr k) = Int.repr (c / m).
Proof.
  intros k m c -> Hk Hc. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. auto.
Qed.

Lemma ru8_land63: forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma ru8_and63: forall x, 0 <= x <= Int.max_unsigned -> Int.and (Int.repr x) (Int.repr 63) = Int.repr (x mod 64).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. f_equal. apply ru8_land63. Qed.

(* Side conditions of the rewrites above: constants, and bounds of quotients and remainders. *)
Ltac ru8_side := first [ reflexivity | rep_lia | (Z.to_euclidean_division_equations; rep_lia) ].

Lemma ru8_upd2: forall (old: list val) v0 v1, Zlength old = 2 -> upd_Znth 1 (upd_Znth 0 old v0) v1 = [v0; v1].
Proof. intros. list_solve. Qed.
Lemma ru8_upd3: forall (old: list val) v0 v1 v2, Zlength old = 3 ->
  upd_Znth 2 (upd_Znth 1 (upd_Znth 0 old v0) v1) v2 = [v0; v1; v2].
Proof. intros. list_solve. Qed.
Lemma ru8_upd4: forall (old: list val) v0 v1 v2 v3, Zlength old = 4 ->
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 old v0) v1) v2) v3 = [v0; v1; v2; v3].
Proof. intros. list_solve. Qed.

(* The stored octets as computed by forward (Int operators, or Z.lor/Z.land after simplification) rewritten to
   [Int.zero_ext 8 (Int.repr v)], v in the model's arithmetic. *)
Ltac ru8_norm :=
  rewrite ?(ru8_shru_div 18 262144), ?(ru8_shru_div 12 4096), ?(ru8_shru_div 6 64) by ru8_side;
  rewrite ?ru8_and63 by ru8_side; rewrite ?ru8_land63;
  rewrite ?(ru8_or_plus 3 8 240), ?(ru8_or_plus 4 16 224), ?(ru8_or_plus 5 32 192), ?(ru8_or_plus 6 64 128)
    by ru8_side;
  rewrite ?(ru8_lor_plus 6 64 128) by ru8_side.

(* After the stored octets are rewritten to [Int.zero_ext 8 (Int.repr v)] with v the model's octet: the octets fit,
   and the array is the model's. *)
Ltac ru8_fin :=
  repeat (rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by ru8_side; change (two_p 8) with 256; ru8_side));
  rewrite ?ru8_upd2, ?ru8_upd3, ?ru8_upd4 by assumption;
  unfold vb; simpl map; apply derives_refl.

Lemma body_utf8 : semax_body [] [] f_utf8 utf8_spec.
Proof.
  start_function.
  forward_if (PROP (128 <= c) LOCAL (temp _c (Vint (Int.repr c)); temp _o o)
    SEP (data_at sh (tarray tuchar (Zlength (utf8 c))) old o)).
  { assert (E: utf8 c = [c]) by (unfold utf8; rewrite (proj2 (Z.ltb_lt _ _)) by lia; auto).
    rewrite E in *. change (Zlength [c]) with 1 in *.
    forward. forward. rewrite E. entailer!.
    rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    replace (upd_Znth 0 old (Vint (Int.repr c))) with [Vint (Int.repr c)] by list_solve. apply derives_refl. }
  { forward. entailer!. }
  forward_if (PROP (2048 <= c) LOCAL (temp _c (Vint (Int.repr c)); temp _o o)
    SEP (data_at sh (tarray tuchar (Zlength (utf8 c))) old o)).
  { assert (E: utf8 c = [192 + c / 64; 128 + c mod 64])
      by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_lt c 2048)) by lia; auto).
    rewrite E in *. change (Zlength [192 + c / 64; 128 + c mod 64]) with 2 in *.
    forward. forward. forward.
    rewrite E. entailer!.
    ru8_norm. ru8_fin. }
  { forward. entailer!. }
  forward_if (PROP (65536 <= c) LOCAL (temp _c (Vint (Int.repr c)); temp _o o)
    SEP (data_at sh (tarray tuchar (Zlength (utf8 c))) old o)).
  { assert (E: utf8 c = [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64])
      by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_ge c 2048)), (proj2 (Z.ltb_lt c 65536)) by lia; auto).
    rewrite E in *. change (Zlength [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64]) with 3 in *.
    forward. forward. forward. forward.
    rewrite E. entailer!. ru8_norm. ru8_fin. }
  { forward. entailer!. }
  Intros.
  assert (E: utf8 c = [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64])
    by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_ge c 2048)), (proj2 (Z.ltb_ge c 65536)),
          (proj2 (Z.leb_le c 1114111)) by lia; auto).
  rewrite E in *.
  change (Zlength [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64]) with 4 in *.
  forward. forward. forward. forward. forward.
  rewrite E. entailer!. ru8_norm. ru8_fin.
Qed.
