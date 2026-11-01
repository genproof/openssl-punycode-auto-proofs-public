(* What the law rj_decode_invalid checks, as a fact about the model (plain Coq): Model.decode fails when an octet
   before the last delimiter is not basic (>= 128), or when an octet of the deltas (from the position after the last
   delimiter, or from 0 when there is none or it is the first octet) has no digit-value.  The first case is caught by
   the basic-prefix test of decode; in the second, steps reads every octet from its start to the end of the input
   through digits (each delta consumes at least one octet and digits fails on an octet without digit-value), so it
   reaches the bad octet and fails.  Then PunySpec.decode_result returns 0 with the length unchanged. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.

(* Where the deltas start, as the harness computes it from last_delimiter. *)
Definition jdi_start (inp: list Z) : Z := if last_delim inp =? 0 then 0 else last_delim inp + 1.

(* The octet at q is one the harness flags: not basic before the last delimiter, or without digit-value in the
   deltas. *)
Definition jdi_bad (inp: list Z) (q: Z) : Prop :=
  (q < last_delim inp /\ 128 <= Znth q inp) \/ (jdi_start inp <= q /\ digit_value (Znth q inp) = 36).

Lemma last_delim_from_range l: forall j acc, 0 <= acc <= j -> 0 <= last_delim_from l j acc <= j + Zlength l.
Proof.
  induction l as [ | c l IH]; intros j acc H; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    specialize (IH (j + 1) (if c =? 45 then j else acc)). destruct (c =? 45); lia.
Qed.

Lemma last_delim_range l: 0 <= last_delim l <= Zlength l.
Proof. unfold last_delim. pose proof (last_delim_from_range l 0 0). lia. Qed.

(* basic_prefix stops before a non-basic octet. *)
Lemma basic_prefix_short l x: In x l -> 128 <= x -> Zlength (basic_prefix l) < Zlength l.
Proof.
  induction l as [ | c l IH]; intros Hin Hx; [ contradiction | ].
  simpl. rewrite Zlength_cons. destruct Hin as [-> | Hin].
  - destruct (x <? 128) eqn:E; [ lia | ]. rewrite Zlength_nil. pose proof (Zlength_nonneg l). lia.
  - destruct (c <? 128).
    + rewrite Zlength_cons. specialize (IH Hin Hx). lia.
    + rewrite Zlength_nil. pose proof (Zlength_nonneg l). lia.
Qed.

(* A successful digit loop consumed at least one octet, each with a digit-value. *)
Lemma digits_read inp f: forall pos i w k bias i1 pos1,
  digits inp f pos i w k bias = Some (i1, pos1) ->
  pos < pos1 /\ forall r, pos <= r < pos1 -> digit_value (Znth r inp) < 36.
Proof.
  induction f as [ | f IH]; intros pos i w k bias i1 pos1 H; simpl in H; [ discriminate | ].
  destruct (Zlength inp <=? pos); [ discriminate | ].
  destruct (36 <=? digit_value (Znth pos inp)) eqn:Ed; [ discriminate | ].
  apply Z.leb_gt in Ed.
  destruct (maxint <? i + digit_value (Znth pos inp) * w); [ discriminate | ].
  destruct (digit_value (Znth pos inp) <? threshold k bias).
  - inversion H; subst. split; [ lia | ]. intros r Hr. replace r with pos by lia. exact Ed.
  - destruct (maxint <? w * (36 - threshold k bias)); [ discriminate | ].
    apply IH in H. destruct H as [Hlt Hall]. split; [ lia | ].
    intros r Hr. destruct (Z.eq_dec r pos); [ subst; exact Ed | apply Hall; lia ].
Qed.

(* steps fails when an octet from its position on has no digit-value. *)
Lemma steps_fail inp cap q: digit_value (Znth q inp) = 36 -> q < Zlength inp ->
  forall f pos n i bias out, pos <= q -> Zlength inp - pos <= Z.of_nat f ->
  fst (steps inp f cap pos n i bias out) = false.
Proof.
  intros Hq Hql f. induction f as [ | f IH]; intros pos n i bias out Hp Hf; [ simpl in Hf; lia | ].
  simpl. destruct (Zlength inp <=? pos) eqn:E; [ apply Z.leb_le in E; lia | ].
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1] | ] eqn:Ed; [ | reflexivity ].
  apply digits_read in Ed. destruct Ed as [Hlt Hall].
  destruct (zlt q pos1) as [Hin | Hout]; [ specialize (Hall q ltac:(lia)); lia | ].
  match goal with |- context [if maxint <? ?x then _ else _] => destruct (maxint <? x) end; [ reflexivity | ].
  destruct (cap <=? Zlength out); [ reflexivity | ].
  rewrite Nat2Z.inj_succ in Hf. apply IH; lia.
Qed.

Lemma decode_fails inp cap q: 0 <= q < Zlength inp -> jdi_bad inp q -> fst (decode inp cap) = false.
Proof.
  intros Hq Hbad. unfold decode. pose proof (last_delim_range inp) as Hb.
  destruct (cap <? last_delim inp); [ reflexivity | ].
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp) eqn:Ep; [ reflexivity | ].
  apply Z.ltb_ge in Ep.
  destruct Hbad as [[Hl Hx] | [Hs Hd]].
  - exfalso.
    assert (In (Znth q inp) (sublist 0 (last_delim inp) inp)).
    { replace (Znth q inp) with (Znth q (sublist 0 (last_delim inp) inp)) by (rewrite Znth_sublist by lia; f_equal; lia).
      apply Znth_In. rewrite Zlength_sublist by lia. lia. }
    pose proof (basic_prefix_short _ _ H Hx). rewrite Zlength_sublist in H0 by lia. lia.
  - unfold jdi_start in Hs.
    apply (steps_fail inp cap q Hd ltac:(lia)).
    + destruct (last_delim inp =? 0); lia.
    + rewrite Zlength_correct. destruct (last_delim inp =? 0); lia.
Qed.

(* The harness's check: on a flagged octet, ossl_punycode_decode returns 0 and leaves the length at cap. *)
Lemma jdi_result inp cap init q: 0 <= q < Zlength inp -> jdi_bad inp q ->
  fst (fst (OpensslPunycode.proof.punycode.PunySpec.decode_result inp cap init)) = 0 /\
  snd (OpensslPunycode.proof.punycode.PunySpec.decode_result inp cap init) = cap.
Proof.
  intros Hq Hbad. unfold OpensslPunycode.proof.punycode.PunySpec.decode_result.
  destruct (Int.max_unsigned <=? Zlength inp); [ auto | ].
  pose proof (decode_fails inp cap q Hq Hbad).
  destruct (decode inp cap) as [ok out]. simpl in H. subst ok. auto.
Qed.
