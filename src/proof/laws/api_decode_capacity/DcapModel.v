(* The capacity facts of the model decoder (Model.decode) that law api_decode_capacity checks: a successful decode
   into cap code points with output out decodes the same into any capacity from Zlength out on (in particular
   exactly Zlength out), and fails into Zlength out - 1 when out is not empty.  The capacity is read only by the
   test against the basic prefix and by the test before each insertion; the output grows by one per insertion. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Import ListNotations.
Local Open Scope Z_scope.

Lemma Zlength_insert_at: forall i x l, 0 <= i <= Zlength l -> Zlength (insert_at i x l) = Zlength l + 1.
Proof.
  intros. unfold insert_at. rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

(* The insertion loop: its output on success, from out, is at least as long as out; any capacity from that length
   on gives the same success, any capacity from Zlength out up to below it fails. *)
Lemma steps_cap: forall inp f cap pos n i bias out res,
  steps inp f cap pos n i bias out = (true, res) ->
  Zlength out <= Zlength res /\
  (forall cap', Zlength res <= cap' -> steps inp f cap' pos n i bias out = (true, res)) /\
  (forall cap', Zlength out <= cap' < Zlength res -> fst (steps inp f cap' pos n i bias out) = false).
Proof.
  intros inp f. induction f; intros cap pos n i bias out res H; cbn [steps] in H |- *.
  - inversion H; subst. split; [lia|]. split; [auto|]. intros; lia.
  - destruct (Zlength inp <=? pos).
    { inversion H; subst. split; [lia|]. split; [auto|]. intros; lia. }
    destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|]; [|discriminate].
    destruct (maxint <? n + i1 / (Zlength out + 1)); [discriminate|].
    destruct (cap <=? Zlength out) eqn:E; [discriminate|].
    pose proof (Zlength_nonneg out).
    assert (Hm: 0 <= i1 mod (Zlength out + 1) <= Zlength out)
      by (pose proof (Z.mod_pos_bound i1 (Zlength out + 1)); lia).
    destruct (IHf _ _ _ _ _ _ _ H) as [L [S F]].
    rewrite Zlength_insert_at in L by lia.
    split; [lia|]. split.
    + intros cap' Hc. rewrite (proj2 (Z.leb_gt cap' (Zlength out))) by lia. apply S; auto.
    + intros cap' Hc. destruct (cap' <=? Zlength out) eqn:E'; [reflexivity|].
      apply Z.leb_gt in E'. apply F. rewrite Zlength_insert_at by lia. lia.
Qed.

Lemma basic_prefix_length: forall l, (length (basic_prefix l) <= length l)%nat.
Proof. induction l; simpl; [lia|]. destruct (a <? 128); simpl; lia. Qed.

(* A successful decode gives at least the basic code points: Zlength out >= last_delim inp. *)
Lemma decode_true_cases: forall inp cap out, decode inp cap = (true, out) ->
  last_delim inp <= cap /\
  Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) = last_delim inp /\
  steps inp (length inp) cap (if last_delim inp =? 0 then 0 else last_delim inp + 1) 128 0 72
    (basic_prefix (sublist 0 (last_delim inp) inp)) = (true, out).
Proof.
  intros inp cap out H. unfold decode in H. cbv zeta in H.
  destruct (cap <? last_delim inp) eqn:E1; [discriminate|].
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp) eqn:E2; [discriminate|].
  apply Z.ltb_ge in E1, E2.
  assert (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <= last_delim inp).
  { pose proof (basic_prefix_length (sublist 0 (last_delim inp) inp)).
    rewrite !Zlength_correct in *. pose proof (proj1 (OpensslPunycode.proof.punycode.DecModel.last_delim_range inp)).
    assert (Z.of_nat (length (sublist 0 (last_delim inp) inp)) <= last_delim inp); [|lia].
    rewrite <- Zlength_correct. destruct (Z_le_gt_dec (last_delim inp) (Zlength inp)).
    - rewrite Zlength_sublist by lia. lia.
    - unfold sublist. rewrite Zlength_correct, skipn_length, firstn_length. lia. }
  split; [lia|]. split; [lia|]. exact H.
Qed.

(* Success into cap with out: the same success into every capacity from Zlength out on. *)
Lemma decode_cap_enough: forall inp cap out cap', decode inp cap = (true, out) -> Zlength out <= cap' ->
  decode inp cap' = (true, out).
Proof.
  intros inp cap out cap' H Hc. destruct (decode_true_cases _ _ _ H) as [H1 [H2 H3]].
  destruct (steps_cap _ _ _ _ _ _ _ _ _ H3) as [L [S _]].
  unfold decode. cbv zeta.
  rewrite (proj2 (Z.ltb_ge cap' (last_delim inp))) by lia.
  rewrite (proj2 (Z.ltb_ge _ (last_delim inp))) by lia.
  apply S; auto.
Qed.

(* Success into cap with a non-empty out: failure into Zlength out - 1. *)
Lemma decode_cap_needed: forall inp cap out, decode inp cap = (true, out) -> out <> [] ->
  fst (decode inp (Zlength out - 1)) = false.
Proof.
  intros inp cap out H Hne. destruct (decode_true_cases _ _ _ H) as [H1 [H2 H3]].
  destruct (steps_cap _ _ _ _ _ _ _ _ _ H3) as [L [_ F]].
  unfold decode. cbv zeta.
  destruct (Zlength out - 1 <? last_delim inp) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
  rewrite (proj2 (Z.ltb_ge _ (last_delim inp))) by lia.
  apply F. lia.
Qed.
