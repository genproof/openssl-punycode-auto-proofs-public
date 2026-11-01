(* The output of the reference decoder (Model.decode) holds code points 0 .. maxint, at most cap of them
   (also the output so far on a failure).  Plain Coq. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

Lemma threshold_range: forall k bias, 0 <= threshold k bias <= 36.
Proof.
  intros. unfold threshold.
  destruct (k <=? bias) eqn:E1; [lia|].
  destruct (bias + 26 <=? k) eqn:E2; lia.
Qed.

Lemma digit_value_nonneg: forall c, 0 <= digit_value c.
Proof.
  intros. unfold digit_value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  rewrite ?andb_true_iff, ?andb_false_iff, ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

Lemma digits_nonneg: forall inp fuel pos i w k bias i1 pos1,
  0 <= i -> 0 <= w ->
  digits inp fuel pos i w k bias = Some (i1, pos1) -> 0 <= i1.
Proof.
  intros inp fuel. induction fuel; intros pos i w k bias i1 pos1 Hi Hw H; simpl in H; [discriminate|].
  destruct (Zlength inp <=? pos); [discriminate|].
  pose proof (digit_value_nonneg (Znth pos inp)).
  destruct (36 <=? digit_value (Znth pos inp)); [discriminate|].
  destruct (maxint <? i + digit_value (Znth pos inp) * w); [discriminate|].
  pose proof (threshold_range k bias).
  destruct (digit_value (Znth pos inp) <? threshold k bias).
  - inversion H; subst. nia.
  - destruct (maxint <? w * (36 - threshold k bias)); [discriminate|].
    eapply IHfuel; [| | exact H]; nia.
Qed.

Lemma steps_out_range: forall inp fuel cap pos n i bias out,
  0 <= n -> 0 <= i ->
  Forall (fun c => 0 <= c <= maxint) out -> Zlength out <= cap ->
  Forall (fun c => 0 <= c <= maxint) (snd (steps inp fuel cap pos n i bias out)) /\
  Zlength (snd (steps inp fuel cap pos n i bias out)) <= cap.
Proof.
  intros inp fuel. induction fuel; intros cap pos n i bias out Hn Hi Hf Hl; cbn [steps]; [auto|].
  destruct (Zlength inp <=? pos); [cbn [snd]; auto|].
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|] eqn:D; [|cbn [snd]; auto].
  assert (0 <= i1) by (eapply digits_nonneg; [exact Hi | | exact D]; lia).
  pose proof (Zlength_nonneg out).
  destruct (maxint <? n + i1 / (Zlength out + 1)) eqn:E1; [cbn [snd]; auto|].
  destruct (cap <=? Zlength out) eqn:E2; [cbn [snd]; auto|].
  apply Z.ltb_ge in E1. apply Z.leb_gt in E2.
  assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
  assert (0 <= i1 mod (Zlength out + 1) < Zlength out + 1) by (apply Z.mod_pos_bound; lia).
  apply IHfuel; try lia.
  - unfold insert_at. apply Forall_app; split.
    + apply Forall_sublist; auto.
    + constructor; [lia|]. apply Forall_sublist; auto.
  - unfold insert_at. rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma basic_prefix_range: forall l, Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  Forall (fun c => 0 <= c <= maxint) (basic_prefix l) /\ (length (basic_prefix l) <= length l)%nat.
Proof.
  induction l; intros H; simpl; auto.
  inversion H; subst. destruct IHl as [IH1 IH2]; auto.
  destruct (a <? 128) eqn:E; simpl; [|split; [constructor|lia]].
  apply Z.ltb_lt in E. split; [constructor; auto; unfold maxint; lia | lia].
Qed.

Lemma decode_out_range: forall inp cap,
  bytes_ok inp -> 0 <= cap ->
  Forall (fun c => 0 <= c <= maxint) (snd (decode inp cap)) /\ Zlength (snd (decode inp cap)) <= cap.
Proof.
  intros inp cap OK Hc. unfold decode.
  destruct (cap <? last_delim inp) eqn:E; [simpl; split; auto; rewrite Zlength_nil; lia|].
  apply Z.ltb_ge in E.
  set (b := last_delim inp) in *.
  assert (Hs: Forall (fun b => 0 <= b <= Byte.max_unsigned) (sublist 0 b inp)) by (apply Forall_sublist; exact OK).
  destruct (basic_prefix_range _ Hs) as [H1 H2].
  assert (H3: Zlength (basic_prefix (sublist 0 b inp)) <= cap).
  { rewrite Zlength_correct. unfold sublist in H2 |- *. rewrite skipn_length, firstn_length in H2. lia. }
  destruct (Zlength (basic_prefix (sublist 0 b inp)) <? b); [simpl; auto|].
  apply steps_out_range; auto; lia.
Qed.
