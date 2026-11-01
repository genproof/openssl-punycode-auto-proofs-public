(* Model facts used by the body of ossl_a2ulabel (plain Coq). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.


Lemma a2um_digit_value_nonneg: forall c, 0 <= digit_value c.
Proof.
  intros c. unfold digit_value.
  destruct ((65 <=? c) && (c <=? 90)) eqn:E1; [apply andb_prop in E1; destruct E1 as [E1 _]; apply Z.leb_le in E1; lia|].
  destruct ((97 <=? c) && (c <=? 122)) eqn:E2; [apply andb_prop in E2; destruct E2 as [E2 _]; apply Z.leb_le in E2; lia|].
  destruct ((48 <=? c) && (c <=? 57)) eqn:E3; [apply andb_prop in E3; destruct E3 as [E3 _]; apply Z.leb_le in E3; lia|].
  lia.
Qed.

Lemma a2um_threshold_le: forall k bias, threshold k bias <= 26.
Proof.
  intros k bias. unfold threshold.
  destruct (k <=? bias) eqn:E1; [lia|].
  destruct (bias + 26 <=? k) eqn:E2; [lia|].
  apply Z.leb_gt in E2. lia.
Qed.

Lemma a2um_digits_mono: forall inp f pos i w k bias i1 pos1,
  digits inp f pos i w k bias = Some (i1, pos1) -> 0 <= i -> 0 <= w -> i <= i1.
Proof.
  intros inp f. induction f as [|f IH]; intros pos i w k bias i1 pos1 H Hi Hw; simpl in H; [discriminate|].
  destruct (Zlength inp <=? pos); [discriminate|].
  pose proof (a2um_digit_value_nonneg (Znth pos inp)) as Hd.
  destruct (36 <=? digit_value (Znth pos inp)); [discriminate|].
  destruct (maxint <? i + digit_value (Znth pos inp) * w); [discriminate|].
  destruct (digit_value (Znth pos inp) <? threshold k bias).
  - inversion H; subst. nia.
  - pose proof (a2um_threshold_le k bias).
    destruct (maxint <? w * (36 - threshold k bias)); [discriminate|].
    apply IH in H; nia.
Qed.

Lemma a2um_last_delim_from_range: forall l j acc,
  0 <= acc <= j -> 0 <= last_delim_from l j acc <= j + Zlength l.
Proof.
  induction l as [|c l IH]; intros j acc H; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons. specialize (IH (j + 1) (if c =? 45 then j else acc)).
    destruct (c =? 45); lia.
Qed.

Lemma a2um_basic_prefix: forall l,
  Forall (fun c => 0 <= c) l ->
  Forall (fun c => 0 <= c <= maxint) (basic_prefix l) /\ Zlength (basic_prefix l) <= Zlength l.
Proof.
  induction l as [|c l IH]; intros H; simpl.
  - split; [constructor | rewrite Zlength_nil; lia].
  - inversion H; subst. destruct IH as [IH1 IH2]; auto.
    destruct (c <? 128) eqn:E.
    + apply Z.ltb_lt in E. split; [constructor; auto; unfold maxint; lia|].
      rewrite !Zlength_cons; lia.
    + split; [constructor|]. rewrite Zlength_nil, Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma a2um_insert_at: forall i x l,
  0 <= i <= Zlength l -> 0 <= x <= maxint -> Forall (fun c => 0 <= c <= maxint) l ->
  Forall (fun c => 0 <= c <= maxint) (insert_at i x l) /\ Zlength (insert_at i x l) = Zlength l + 1.
Proof.
  intros i x l Hi Hx Hl. unfold insert_at. split.
  - apply Forall_app. split.
    + apply Forall_sublist; auto.
    + constructor; auto. apply Forall_sublist; auto.
  - rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma a2um_steps: forall inp f cap pos n i bias out,
  0 <= n <= maxint -> 0 <= i -> Forall (fun c => 0 <= c <= maxint) out -> Zlength out <= cap ->
  Forall (fun c => 0 <= c <= maxint) (snd (steps inp f cap pos n i bias out)) /\
  Zlength (snd (steps inp f cap pos n i bias out)) <= cap.
Proof.
  intros inp f. induction f as [|f IH]; intros cap pos n i bias out Hn Hi Hout Hc; cbn [steps snd]; try (split; assumption).
  destruct (Zlength inp <=? pos); cbn [snd]; try (split; assumption).
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|] eqn:D; cbn [snd]; try (split; assumption).
  pose proof (a2um_digits_mono _ _ _ _ _ _ _ _ _ D Hi ltac:(lia)) as Hi1.
  pose proof (Zlength_nonneg out) as Hl.
  destruct (maxint <? n + i1 / (Zlength out + 1)) eqn:E1; cbn [snd]; try (split; assumption).
  destruct (cap <=? Zlength out) eqn:E2; cbn [snd]; try (split; assumption).
  apply Z.ltb_ge in E1. apply Z.leb_gt in E2.
  assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound i1 (Zlength out + 1) ltac:(lia)).
  destruct (a2um_insert_at (i1 mod (Zlength out + 1)) (n + i1 / (Zlength out + 1)) out ltac:(lia) ltac:(lia) Hout)
    as [F L].
  apply IH; auto; lia.
Qed.

(* The output of the decoder (also the output so far on failure) holds code points 0 .. maxint, at most cap of
   them. *)
Lemma decode_out_range: forall inp cap,
  bytes_ok inp -> 0 <= cap ->
  Forall (fun c => 0 <= c <= maxint) (snd (decode inp cap)) /\ Zlength (snd (decode inp cap)) <= cap.
Proof.
  intros inp cap OK Hcap. unfold decode.
  pose proof (a2um_last_delim_from_range inp 0 0 ltac:(lia)) as Hb. fold (last_delim inp) in Hb.
  assert (OK0: Forall (fun c => 0 <= c) (sublist 0 (last_delim inp) inp)).
  { apply Forall_sublist. eapply Forall_impl; [|exact OK]. simpl; intros; lia. }
  destruct (a2um_basic_prefix _ OK0) as [F L].
  rewrite Zlength_sublist in L by lia.
  destruct (cap <? last_delim inp) eqn:E1; simpl.
  { split; [constructor | rewrite Zlength_nil; lia]. }
  apply Z.ltb_ge in E1.
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp) eqn:E2; simpl.
  { split; auto. lia. }
  apply a2um_steps; auto. unfold maxint; lia. lia. lia.
Qed.
