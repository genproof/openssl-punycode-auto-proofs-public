(* Law rfc_unique, model part 1: the digits of a generalized variable-length integer are unique (RFC 3492 3.3).
   Two runs of Model.digits from the same state that reach the same value read digit strings of the same length
   with the same digit-values (plain Coq). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

Lemma run_threshold_range: forall k bias, 1 <= threshold k bias <= 26.
Proof.
  intros. unfold threshold.
  destruct (k <=? bias) eqn:E1; [lia|].
  destruct (bias + 26 <=? k) eqn:E2; rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

Lemma run_digit_value_range: forall c, 0 <= digit_value c <= 36.
Proof.
  intros. unfold digit_value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  rewrite ?andb_true_iff, ?andb_false_iff, ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

(* A successful digit loop adds a nonnegative multiple of the weight w, and reads at least one octet of the
   input. *)
Lemma run_digits_shape: forall inp fuel pos i w k bias i1 pos1,
  0 < w -> 0 <= pos ->
  digits inp fuel pos i w k bias = Some (i1, pos1) ->
  (exists X, 0 <= X /\ i1 = i + w * X) /\ pos < pos1 <= Zlength inp.
Proof.
  intros inp fuel. induction fuel; intros pos i w k bias i1 pos1 Hw Hp H; cbn [digits] in H; [discriminate|].
  destruct (Zlength inp <=? pos) eqn:El; [discriminate|].
  pose proof (run_digit_value_range (Znth pos inp)).
  destruct (36 <=? digit_value (Znth pos inp)) eqn:E36; [discriminate|].
  destruct (maxint <? i + digit_value (Znth pos inp) * w); [discriminate|].
  pose proof (run_threshold_range k bias).
  rewrite Z.leb_gt in El, E36.
  destruct (digit_value (Znth pos inp) <? threshold k bias).
  - inversion H; subst. split; [exists (digit_value (Znth pos inp)); split; lia | lia].
  - destruct (maxint <? w * (36 - threshold k bias)); [discriminate|].
    apply IHfuel in H; [|nia|lia]. destruct H as [[X [HX ->]] Hp1].
    split; [|lia].
    exists (digit_value (Znth pos inp) + (36 - threshold k bias) * X). split; nia.
Qed.

Lemma run_digits_unique: forall inpA fuelA inpB fuelB pos i w k bias i1 pA pB,
  0 < w -> 0 <= pos ->
  digits inpA fuelA pos i w k bias = Some (i1, pA) ->
  digits inpB fuelB pos i w k bias = Some (i1, pB) ->
  pA = pB /\
  forall j, pos <= j < pA ->
    digit_value (Znth j inpA) = digit_value (Znth j inpB) /\ digit_value (Znth j inpA) < 36.
Proof.
  intros inpA fuelA. induction fuelA;
    intros inpB fuelB pos i w k bias i1 pA pB Hw Hp HA HB; cbn [digits] in HA; [discriminate|].
  destruct fuelB as [|fuelB]; cbn [digits] in HB; [discriminate|].
  destruct (Zlength inpA <=? pos) eqn:ElA; [discriminate|].
  destruct (Zlength inpB <=? pos) eqn:ElB; [discriminate|].
  set (dA := digit_value (Znth pos inpA)) in *.
  set (dB := digit_value (Znth pos inpB)) in *.
  pose proof (run_digit_value_range (Znth pos inpA)).
  pose proof (run_digit_value_range (Znth pos inpB)).
  fold dA dB in H, H0.
  destruct (36 <=? dA) eqn:EA; [discriminate|].
  destruct (36 <=? dB) eqn:EB; [discriminate|].
  rewrite Z.leb_gt in EA, EB.
  destruct (maxint <? i + dA * w); [discriminate|].
  destruct (maxint <? i + dB * w); [discriminate|].
  pose proof (run_threshold_range k bias).
  set (t := threshold k bias) in *.
  destruct (dA <? t) eqn:TA; destruct (dB <? t) eqn:TB; rewrite ?Z.ltb_lt, ?Z.ltb_ge in TA, TB.
  - inversion HA; inversion HB; subst.
    assert (dA = dB) by nia.
    split; [lia|]. intros j Hj. assert (j = pos) by lia. subst j. split; lia.
  - inversion HA; subst.
    destruct (maxint <? w * (36 - t)); [discriminate|].
    apply run_digits_shape in HB; [|nia|lia]. destruct HB as [[X [HX HXe]] _].
    nia.
  - inversion HB; subst.
    destruct (maxint <? w * (36 - t)); [discriminate|].
    apply run_digits_shape in HA; [|nia|lia]. destruct HA as [[X [HX HXe]] _].
    nia.
  - destruct (maxint <? w * (36 - t)); [discriminate|].
    pose proof HA as HA'. pose proof HB as HB'.
    apply run_digits_shape in HA'; [|nia|lia]. destruct HA' as [[XA [HXA HXAe]] _].
    apply run_digits_shape in HB'; [|nia|lia]. destruct HB' as [[XB [HXB HXBe]] _].
    (* (dA - t) + (36 - t) XA = (dB - t) + (36 - t) XB with both remainders below 36 - t *)
    assert (Hq: dA - t + (36 - t) * XA = dB - t + (36 - t) * XB) by nia.
    assert (Hd: (36 - t) * (XB - XA) = dA - dB) by lia.
    assert (XA = XB).
    { destruct (Z.lt_total XA XB) as [Hl|[Hl|Hl]]; [|exact Hl|].
      - assert ((36 - t) * (XB - XA) >= (36 - t) * 1) by (apply Zmult_ge_compat_l; lia). lia.
      - assert ((36 - t) * (XA - XB) >= (36 - t) * 1) by (apply Zmult_ge_compat_l; lia). lia. }
    subst XB. assert (dA = dB) by lia.
    rewrite H2 in HA.
    destruct (IHfuelA inpB fuelB (pos + 1) (i + dB * w) (w * (36 - t)) (k + 36) bias i1 pA pB
      ltac:(nia) ltac:(lia) HA HB) as [Heq Hj].
    split; [exact Heq|]. intros j Hj'.
    destruct (Z.eq_dec j pos); [subst j; split; lia|]. apply Hj; lia.
Qed.
