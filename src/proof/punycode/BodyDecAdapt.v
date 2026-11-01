(* The body of adapt (crypto/punycode.c), under Punycode.CS; split from BodyDecHelpers.v for the per-file time
   budget. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.

(* One iteration of adapt's loop: delta > 455 and delta * 35^j <= d0 < 2^32 bound j by 4, so fuel is left. *)
Lemma adapt_loop_step: forall j d d0,
  0 <= j <= 5 -> 0 <= d -> d * 35 ^ j <= d0 -> d0 <= Int.max_unsigned -> 455 < d ->
  j + 1 <= 5 /\ d / 35 * 35 ^ (j + 1) <= d0 /\
  adapt_loop (Z.to_nat (64 - (j + 1))) (d / 35) (36 * (j + 1)) = adapt_loop (Z.to_nat (64 - j)) d (36 * j).
Proof.
  intros j d d0 Hj Hd Hb Hm Hgt.
  assert (Hj4: j <= 4).
  { destruct (Z.eq_dec j 5); [subst j; simpl in Hb; rep_lia | lia]. }
  split; [lia|]. split.
  - rewrite Z.pow_add_r by lia. rewrite Z.mul_assoc.
    assert (d / 35 * 35 ^ 1 <= d) by (simpl; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (0 < 35 ^ j) by (apply Z.pow_pos_nonneg; lia).
    nia.
  - replace (Z.to_nat (64 - j)) with (S (Z.to_nat (64 - (j + 1)))) by lia.
    simpl. destruct (Z.ltb_spec 455 d); [|lia]. f_equal. lia.
Qed.

Lemma adapt_loop_exit: forall j d,
  0 <= j <= 5 -> 0 <= d <= 455 ->
  adapt_loop (Z.to_nat (64 - j)) d (36 * j) = 36 * j + 36 * d / (d + 38).
Proof.
  intros j d Hj Hd.
  replace (Z.to_nat (64 - j)) with (S (Z.to_nat (64 - (j + 1)))) by lia.
  simpl. destruct (Z.ltb_spec 455 d); [lia|]. reflexivity.
Qed.

Ltac fix455 :=
  match goal with H: context [Int.unsigned (Int.divu (Int.mul (Int.repr (36 - 1)) (Int.repr 26)) (Int.repr 2))] |- _ =>
    change (Int.unsigned (Int.divu (Int.mul (Int.repr (36 - 1)) (Int.repr 26)) (Int.repr 2))) with 455 in H end.

Lemma adapt_unfold: forall delta np ft,
  adapt delta np (negb (ft =? 0)) =
  adapt_loop 64 ((if ft =? 0 then delta / 2 else delta / 700) + (if ft =? 0 then delta / 2 else delta / 700) / np) 0.
Proof. intros. unfold adapt. destruct (ft =? 0); reflexivity. Qed.

(* Keeps VST's simplifications from unfolding the model's 64-step loop in the postcondition. *)
Local Opaque adapt.

Lemma body_adapt_aux : semax_body Vprog Gprog_none f_adapt adapt_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP() LOCAL(temp _t'1 (Vint (Int.repr (if firsttime =? 0 then delta / 2 else delta / 700)));
     temp _k (Vint (Int.repr 0)); temp _delta (Vint (Int.repr delta)); temp _numpoints (Vint (Int.repr numpoints));
     gvars gv)
    SEP(puny_consts gv)).
  { unfold puny_consts; Intros. forward. forward. unfold puny_consts. entailer!.
    destruct (Z.eqb_spec firsttime 0); [lia|auto]. }
  { forward. entailer!. destruct (Z.eqb_spec firsttime 0); [auto|]. apply repr_inj_unsigned in H2; rep_lia. }
  forward.
  remember (if firsttime =? 0 then delta / 2 else delta / 700) as d1 eqn:Ed1.
  assert (Hd1: 0 <= d1 <= 2147483647).
  { rewrite Ed1. destruct (firsttime =? 0); split.
    - apply Z.div_pos; lia.
    - assert (delta / 2 < 2147483648) by (apply Z.div_lt_upper_bound; rep_lia). lia.
    - apply Z.div_pos; lia.
    - assert (delta / 700 < 2147483648) by (apply Z.div_lt_upper_bound; rep_lia). lia. }
  assert (Hd1n: 0 <= d1 / numpoints <= d1).
  { split. apply Z.div_pos; lia. apply Z.div_le_upper_bound; nia. }
  forward.
  { entailer!. apply repr_inj_unsigned in H2; rep_lia. }
  remember (d1 + d1 / numpoints) as d0 eqn:Ed0.
  assert (Hexp: Int.add (Int.repr d1) (Int.divu (Int.repr d1) (Int.repr numpoints)) = Int.repr d0).
  { unfold Int.divu, Int.add.
    rewrite (Int.unsigned_repr numpoints), (Int.unsigned_repr d1), (Int.unsigned_repr (d1 / numpoints)) by rep_lia.
    rewrite Ed0; reflexivity. }
  rewrite Hexp.
  assert (Hd0: 0 <= d0 <= Int.max_unsigned) by (rewrite Ed0; rep_lia).
  assert (Hm: adapt delta numpoints (negb (firsttime =? 0)) = adapt_loop 64 d0 0).
  { rewrite adapt_unfold, Ed0, Ed1. reflexivity. }
  clear Hexp Ed0 Ed1.
  forward_loop (EX j: Z, EX d: Z,
      PROP (0 <= j <= 5; 0 <= d; d * 35 ^ j <= d0;
            adapt_loop (Z.to_nat (64 - j)) d (36 * j) = adapt_loop 64 d0 0)
      LOCAL (temp _delta (Vint (Int.repr d)); temp _k (Vint (Int.repr (36 * j))); gvars gv)
      SEP (puny_consts gv))
    break: (EX j: Z, EX d: Z,
      PROP (0 <= j <= 5; 0 <= d <= 455;
            adapt_loop (Z.to_nat (64 - j)) d (36 * j) = adapt_loop 64 d0 0)
      LOCAL (temp _delta (Vint (Int.repr d)); temp _k (Vint (Int.repr (36 * j))); gvars gv)
      SEP (puny_consts gv)).
  { Exists 0 d0. entailer!. }
  { Intros j d. unfold puny_consts; Intros. forward. forward. forward.
    forward_if.
    { fix455.
      forward. forward. forward. forward. forward.
      destruct (adapt_loop_step j d d0) as (? & ? & ?); auto; try lia.
      Exists (j + 1) (d / 35). unfold puny_consts. entailer!.
      repeat split; try apply Z.div_pos; try lia; try congruence; f_equal; f_equal; lia. }
    { fix455.
      forward. unfold puny_consts. Exists j d. entailer!. }
  }
  Intros j d. unfold puny_consts; Intros. forward. forward. forward. forward.
  { entailer!. apply repr_inj_unsigned in H23; rep_lia. }
  unfold puny_consts. entailer!.
  rewrite Hm, <- H4, adapt_loop_exit by lia. reflexivity.
Qed.
