(* The model fact of law rfc_digit_case (plain Coq): Model.decode does not see the case of the letters of the
   deltas.  An input bs' that has the octets of bs before the deltas (positions below delta_start bs) and, at every
   position, an octet equal to that of bs up to the case of a letter, decodes as bs does: the two have the same
   delimiters '-' (so the same last_delim and literal part) and the same digit-values. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.punycode.PunySpec.
Local Open Scope bool_scope.

(* The lowercase form of an octet: an uppercase letter moved to lowercase, any other octet unchanged. *)
Definition lower (c: Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

(* Where the deltas start: after the last '-', or at 0 when there is none or it is the first octet (as decode and
   the harness's loop compute it). *)
Definition delta_start (bs: list Z) : Z := if last_delim bs =? 0 then 0 else last_delim bs + 1.

(* bs' is bs with letters at positions from s on in either case. *)
Definition case_rel (s: Z) (bs bs': list Z) : Prop :=
  Zlength bs' = Zlength bs /\
  (forall j, 0 <= j < Zlength bs -> j < s -> Znth j bs' = Znth j bs) /\
  (forall j, 0 <= j < Zlength bs -> lower (Znth j bs') = lower (Znth j bs)).

Lemma digit_value_lower a b: lower a = lower b -> digit_value a = digit_value b.
Proof.
  unfold lower, digit_value. intros E.
  destruct ((65 <=? a) && (a <=? 90)) eqn:Ea, ((65 <=? b) && (b <=? 90)) eqn:Eb;
  repeat match goal with
         | H: (_ && _) = true |- _ => apply andb_prop in H; destruct H
         | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
         end;
  try (assert (a = b) by lia; subst; reflexivity);
  repeat match goal with |- context [ (?x <=? ?y) ] => destruct (Z.leb_spec x y) end; simpl;
  try lia; try (rewrite andb_false_iff in *; repeat rewrite Z.leb_gt in *; lia).
Qed.

Lemma dash_lower a b: lower a = lower b -> (a =? 45) = (b =? 45).
Proof.
  unfold lower. intros E.
  destruct ((65 <=? a) && (a <=? 90)) eqn:Ea, ((65 <=? b) && (b <=? 90)) eqn:Eb;
  repeat match goal with
         | H: (_ && _) = true |- _ => apply andb_prop in H; destruct H
         | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
         | H: (_ && _) = false |- _ => apply andb_false_iff in H; destruct H
         | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
         end;
  destruct (Z.eqb_spec a 45), (Z.eqb_spec b 45); auto; lia.
Qed.

Lemma Forall2_of_Znth (P: Z -> Z -> Prop) l l':
  Zlength l = Zlength l' -> (forall j, 0 <= j < Zlength l -> P (Znth j l) (Znth j l')) -> Forall2 P l l'.
Proof.
  revert l'. induction l as [| a l IH]; intros [| b l'] E H.
  - constructor.
  - rewrite Zlength_nil, Zlength_cons in E. pose proof (Zlength_nonneg l'). lia.
  - rewrite Zlength_nil, Zlength_cons in E. pose proof (Zlength_nonneg l). lia.
  - rewrite !Zlength_cons in E. constructor.
    + specialize (H 0). rewrite !Znth_0_cons in H. apply H. pose proof (Zlength_nonneg l). rewrite Zlength_cons. lia.
    + apply IH; [ lia | ]. intros j Hj. specialize (H (j + 1)).
      rewrite !Znth_pos_cons in H by lia. replace (j + 1 - 1) with j in H by lia. apply H.
      rewrite Zlength_cons. lia.
Qed.

Lemma last_delim_from_same l l' j acc:
  Forall2 (fun a b => (a =? 45) = (b =? 45)) l l' -> last_delim_from l j acc = last_delim_from l' j acc.
Proof.
  intros H. revert j acc. induction H as [| a b l l' Hab _ IH]; intros j acc; simpl; [ reflexivity | ].
  rewrite Hab. apply IH.
Qed.

Section Rel.
Variables bs bs': list Z.
Variable s: Z.
Hypothesis Hs: 0 <= s.
Hypothesis R: case_rel s bs bs'.

Lemma rel_digits fuel pos i w k bias:
  s <= pos -> digits bs' fuel pos i w k bias = digits bs fuel pos i w k bias.
Proof.
  destruct R as [HL [_ HC]].
  revert pos i w k bias. induction fuel as [| f IH]; intros pos i w k bias Hp; simpl; [ reflexivity | ].
  rewrite HL. destruct (Zlength bs <=? pos) eqn:E; [ reflexivity | ].
  apply Z.leb_gt in E.
  rewrite (digit_value_lower _ _ (HC pos ltac:(lia))).
  destruct (36 <=? digit_value (Znth pos bs)); [ reflexivity | ].
  destruct (maxint <? i + digit_value (Znth pos bs) * w); [ reflexivity | ].
  destruct (digit_value (Znth pos bs) <? threshold k bias); [ reflexivity | ].
  destruct (maxint <? w * (36 - threshold k bias)); [ reflexivity | ].
  apply IH. lia.
Qed.

Lemma digits_pos l fuel pos i w k bias i1 pos1:
  digits l fuel pos i w k bias = Some (i1, pos1) -> pos < pos1.
Proof.
  revert pos i w k bias. induction fuel as [| f IH]; intros pos i w k bias H; simpl in H; [ discriminate | ].
  destruct (Zlength l <=? pos); [ discriminate | ].
  destruct (36 <=? digit_value (Znth pos l)); [ discriminate | ].
  destruct (maxint <? i + digit_value (Znth pos l) * w); [ discriminate | ].
  destruct (digit_value (Znth pos l) <? threshold k bias).
  - inversion H. lia.
  - destruct (maxint <? w * (36 - threshold k bias)); [ discriminate | ].
    apply IH in H. lia.
Qed.

Lemma rel_steps fuel cap pos n i bias out:
  s <= pos -> steps bs' fuel cap pos n i bias out = steps bs fuel cap pos n i bias out.
Proof.
  destruct R as [HL _].
  revert pos n i bias out. induction fuel as [| f IH]; intros pos n i bias out Hp; simpl; [ reflexivity | ].
  rewrite HL. destruct (Zlength bs <=? pos); [ reflexivity | ].
  rewrite (rel_digits _ _ _ _ _ _ Hp).
  destruct (digits bs (Z.to_nat (Zlength bs - pos)) pos i 1 36 bias) as [[i1 pos1] |] eqn:E; [ | reflexivity ].
  apply digits_pos in E.
  repeat match goal with |- (if ?b then _ else _) = (if ?b then _ else _) => destruct b; [ reflexivity | ] end.
  apply IH. lia.
Qed.

End Rel.

(* The case of the letters of the deltas does not change what decode gives. *)
Lemma decode_case bs bs' cap:
  case_rel (delta_start bs) bs bs' -> decode bs' cap = decode bs cap.
Proof.
  intros R. pose proof R as [HL [HP HC]].
  assert (Hd: last_delim bs' = last_delim bs).
  { unfold last_delim. symmetry. apply last_delim_from_same.
    apply Forall2_of_Znth; [ lia | ]. intros j Hj. symmetry. apply dash_lower, HC. lia. }
  pose proof (OpensslPunycode.proof.punycode.DecModel.last_delim_range bs) as [Hr0 Hr].
  assert (Hb: last_delim bs <= Zlength bs) by (pose proof (Zlength_nonneg bs); destruct Hr; lia).
  assert (Hsub: sublist 0 (last_delim bs) bs' = sublist 0 (last_delim bs) bs).
  { apply Znth_eq_ext.
    - rewrite !Zlength_sublist; lia.
    - intros j Hj. rewrite Zlength_sublist in Hj by lia.
      rewrite !Znth_sublist by lia. replace (j + 0) with j by lia.
      apply HP; [ lia | ]. unfold delta_start. destruct (Z.eqb_spec (last_delim bs) 0); lia. }
  assert (Hs: 0 <= delta_start bs) by (unfold delta_start; destruct (last_delim bs =? 0); lia).
  unfold decode. rewrite Hd, Hsub.
  replace (length bs') with (length bs) by (rewrite !Zlength_correct in HL; lia).
  destruct (cap <? last_delim bs); [ reflexivity | ].
  destruct (Zlength (basic_prefix (sublist 0 (last_delim bs) bs)) <? last_delim bs); [ reflexivity | ].
  apply (rel_steps bs bs' (delta_start bs) Hs R). apply Z.le_refl.
Qed.
