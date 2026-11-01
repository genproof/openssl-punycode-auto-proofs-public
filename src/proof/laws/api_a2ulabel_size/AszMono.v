(* Law api_a2ulabel_size: the capacity only decides whether the output fits.  A conversion that succeeds (result 1)
   writing w succeeds the same way in every capacity of at least Zlength w octets, and gives 0 ("too small") in
   every smaller capacity: the result -1 does not depend on the capacity, and a run whose writes all fit writes
   the same octets whatever the room left. *)
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* put: a sink that comes out not short went in not short, and the octets written only grow. *)
Lemma put_mono cap k bs:
  (snd (put cap k bs) = false -> snd k = false) /\ Zlength (fst k) <= Zlength (fst (put cap k bs)).
Proof.
  unfold put. destruct (Zlength bs =? 0); [split; auto; lia|].
  destruct (cap - Zlength (fst k) <? Zlength bs); simpl.
  - split; [discriminate | lia].
  - rewrite Zlength_app. pose proof (Zlength_nonneg bs). split; auto; lia.
Qed.

(* put: a write that fits and leaves the sink not short is the same in every capacity the result fits in. *)
Lemma put_fit cap1 cap2 k bs:
  snd (put cap1 k bs) = false -> Zlength (fst (put cap1 k bs)) <= cap2 -> put cap2 k bs = put cap1 k bs.
Proof.
  unfold put. destruct (Zlength bs =? 0); auto.
  destruct (cap1 - Zlength (fst k) <? Zlength bs); simpl; [discriminate|].
  intros _ H. rewrite Zlength_app in H.
  destruct (cap2 - Zlength (fst k) <? Zlength bs) eqn:E; auto. apply Z.ltb_lt in E. lia.
Qed.

(* put never writes past the capacity. *)
Lemma put_inv cap k bs: Zlength (fst k) <= cap -> Zlength (fst (put cap k bs)) <= cap.
Proof.
  unfold put. destruct (Zlength bs =? 0); auto.
  destruct (cap - Zlength (fst k) <? Zlength bs) eqn:E; simpl; auto.
  apply Z.ltb_ge in E. rewrite Zlength_app. lia.
Qed.

(* The same four facts for the UTF-8 writes, one label, and the whole conversion. *)
Lemma pu_mono cap k cps:
  (snd (snd (put_utf8s cap k cps)) = false -> snd k = false)
  /\ Zlength (fst k) <= Zlength (fst (snd (put_utf8s cap k cps))).
Proof.
  revert k; induction cps as [|c r IH]; intro k; simpl; [split; auto; lia|].
  destruct (Zlength (utf8 c) =? 0); simpl; [split; auto; lia|].
  destruct (IH (put cap k (utf8 c))) as [A B]. destruct (put_mono cap k (utf8 c)) as [C D].
  split; [tauto | lia].
Qed.

Lemma pu_fit cap1 cap2 k cps:
  snd (snd (put_utf8s cap1 k cps)) = false -> Zlength (fst (snd (put_utf8s cap1 k cps))) <= cap2 ->
  put_utf8s cap2 k cps = put_utf8s cap1 k cps.
Proof.
  revert k; induction cps as [|c r IH]; intro k; simpl; auto.
  destruct (Zlength (utf8 c) =? 0); auto. intros H1 H2.
  destruct (pu_mono cap1 (put cap1 k (utf8 c)) r) as [A B].
  rewrite (put_fit cap1 cap2); auto; lia.
Qed.

Lemma pu_inv cap k cps: Zlength (fst k) <= cap -> Zlength (fst (snd (put_utf8s cap k cps))) <= cap.
Proof.
  revert k; induction cps as [|c r IH]; intro k; simpl; auto.
  destruct (Zlength (utf8 c) =? 0); auto. intro H. apply IH, put_inv, H.
Qed.

(* Whether the code points are all encodable does not depend on the sink nor the capacity. *)
Lemma pu_ok cap cap' k k' cps: fst (put_utf8s cap k cps) = fst (put_utf8s cap' k' cps).
Proof.
  revert k k'; induction cps as [|c r IH]; intros k k'; simpl; auto.
  destruct (Zlength (utf8 c) =? 0); auto.
Qed.

Lemma ls_mono cap k l:
  (snd (snd (label_step cap k l)) = false -> snd k = false)
  /\ Zlength (fst k) <= Zlength (fst (snd (label_step cap k l))).
Proof.
  unfold label_step. destruct (is_ace l); [|apply put_mono].
  destruct (maxint <=? _); [simpl; split; auto; lia|].
  destruct (decode _ label_cap) as [[|] cps]; [apply pu_mono | simpl; split; auto; lia].
Qed.

Lemma ls_fit cap1 cap2 k l:
  snd (snd (label_step cap1 k l)) = false -> Zlength (fst (snd (label_step cap1 k l))) <= cap2 ->
  label_step cap2 k l = label_step cap1 k l.
Proof.
  unfold label_step. destruct (is_ace l).
  - destruct (maxint <=? _); auto.
    destruct (decode _ label_cap) as [[|] cps]; auto. apply pu_fit.
  - simpl. intros. f_equal. apply put_fit; auto.
Qed.

Lemma ls_inv cap k l: Zlength (fst k) <= cap -> Zlength (fst (snd (label_step cap k l))) <= cap.
Proof.
  unfold label_step. destruct (is_ace l); [|apply put_inv].
  destruct (maxint <=? _); auto.
  destruct (decode _ label_cap) as [[|] cps]; auto. apply pu_inv.
Qed.

Lemma ls_ok cap cap' k k' l: fst (label_step cap k l) = fst (label_step cap' k' l).
Proof.
  unfold label_step. destruct (is_ace l); auto.
  destruct (maxint <=? _); auto.
  destruct (decode _ label_cap) as [[|] cps]; auto. apply pu_ok.
Qed.

Lemma al_mono cap k ls:
  (snd (snd (a2u_labels cap k ls)) = false -> snd k = false)
  /\ Zlength (fst k) <= Zlength (fst (snd (a2u_labels cap k ls))).
Proof.
  revert k; induction ls as [|l ls IH]; intro k; simpl; [apply put_mono|].
  destruct (ls_mono cap k l) as [A B].
  destruct (label_step cap k l) as [ok k1]; simpl in A, B.
  destruct ok; [|simpl; auto].
  destruct ls as [|l' ls'].
  - destruct (put_mono cap k1 [0]) as [C D]. simpl. split; [tauto | lia].
  - destruct (put_mono cap k1 [46]) as [C D]. destruct (IH (put cap k1 [46])) as [E F].
    split; [tauto | lia].
Qed.

Lemma al_fit cap1 cap2 k ls:
  snd (snd (a2u_labels cap1 k ls)) = false -> Zlength (fst (snd (a2u_labels cap1 k ls))) <= cap2 ->
  a2u_labels cap2 k ls = a2u_labels cap1 k ls.
Proof.
  revert k; induction ls as [|l ls IH]; intro k; simpl.
  - intros H1 H2. rewrite (put_fit cap1 cap2); auto.
  - destruct (ls_mono cap1 k l) as [A B].
    destruct (label_step cap1 k l) as [ok k1] eqn:E; simpl in A, B.
    destruct ok.
    + destruct ls as [|l' ls'].
      * simpl. intros H1 H2. destruct (put_mono cap1 k1 [0]) as [C D].
        rewrite (ls_fit cap1 cap2), E by (rewrite E; simpl; auto; lia).
        rewrite (put_fit cap1 cap2); auto.
      * intros H1 H2. destruct (al_mono cap1 (put cap1 k1 [46]) (l' :: ls')) as [C D].
        destruct (put_mono cap1 k1 [46]) as [F G].
        rewrite (ls_fit cap1 cap2), E by (rewrite E; simpl; auto; lia).
        rewrite (put_fit cap1 cap2) by (auto; lia).
        apply IH; auto.
    + simpl. intros H1 H2. rewrite (ls_fit cap1 cap2), E by (rewrite E; simpl; auto; lia). auto.
Qed.

Lemma al_inv cap k ls: Zlength (fst k) <= cap -> Zlength (fst (snd (a2u_labels cap k ls))) <= cap.
Proof.
  revert k; induction ls as [|l ls IH]; intros k H; simpl; [apply put_inv; auto|].
  pose proof (ls_inv cap k l H) as A.
  destruct (label_step cap k l) as [ok k1]; simpl in A.
  destruct ok; [|simpl; auto].
  destruct ls as [|l' ls']; [apply put_inv; auto|].
  apply IH, put_inv, A.
Qed.

(* The result is -1 (a label does not convert), 0 (the sink is short) or 1 (the sink is not short); the result -1
   does not depend on the capacity nor the sink. *)
Lemma al_res cap k ls:
  fst (a2u_labels cap k ls) = -1 \/ fst (a2u_labels cap k ls) = 0
  \/ (fst (a2u_labels cap k ls) = 1 /\ snd (snd (a2u_labels cap k ls)) = false).
Proof.
  revert k; induction ls as [|l ls IH]; intro k; simpl.
  - destruct (snd (put cap k [0])) eqn:E; simpl; auto.
  - destruct (label_step cap k l) as [ok k1].
    destruct ok; [|simpl; auto].
    destruct ls as [|l' ls']; [|apply IH].
    destruct (snd (put cap k1 [0])) eqn:E; simpl; auto.
Qed.

Lemma al_fail cap cap' k k' ls:
  fst (a2u_labels cap k ls) = -1 -> fst (a2u_labels cap' k' ls) = -1.
Proof.
  revert k k'; induction ls as [|l ls IH]; intros k k'; simpl.
  - destruct (snd (put cap k [0])); simpl; lia.
  - pose proof (ls_ok cap cap' k k' l) as O.
    destruct (label_step cap k l) as [ok k1], (label_step cap' k' l) as [ok' k1']; simpl in O; subst ok'.
    intro H. destruct ok; simpl.
    + destruct ls as [|l' ls']; [destruct (snd (put cap k1 [0])); simpl in H; lia|]. eapply IH, H.
    + auto.
Qed.

Lemma a2ulabel_fit s cap1 cap2 w:
  a2ulabel s cap1 = (1, w) -> Zlength w <= cap2 -> a2ulabel s cap2 = (1, w).
Proof.
  unfold a2ulabel. intros H1 H2.
  destruct (al_res cap1 ([], false) (labels s)) as [R|[R|[R S]]];
    destruct (a2u_labels cap1 ([], false) (labels s)) as [r k1] eqn:E; simpl in *; inversion H1; subst; try lia.
  rewrite (al_fit cap1 cap2), E by (rewrite E; simpl; auto). reflexivity.
Qed.

Lemma a2ulabel_short s cap1 cap2 w:
  0 <= cap1 -> 0 <= cap2 -> a2ulabel s cap1 = (1, w) -> cap2 < Zlength w -> fst (a2ulabel s cap2) = 0.
Proof.
  intros P1 P2 H1 H2.
  assert (Hw: Zlength w <= cap1).
  { pose proof (al_inv cap1 ([], false) (labels s)) as I. unfold a2ulabel in H1.
    destruct (a2u_labels cap1 ([], false) (labels s)) as [r k1]. inversion H1; subst.
    apply I. simpl. rewrite Zlength_nil. lia. }
  pose proof (al_inv cap2 ([], false) (labels s)) as I.
  pose proof (al_res cap2 ([], false) (labels s)) as R.
  pose proof (al_fail cap2 cap1 ([], false) ([], false) (labels s)) as F.
  assert (H1' := H1). unfold a2ulabel in H1' |- *.
  destruct (a2u_labels cap1 ([], false) (labels s)) as [r1 k1] eqn:E1. inversion H1'; subst.
  destruct (a2u_labels cap2 ([], false) (labels s)) as [r2 k2] eqn:E2. simpl in *.
  specialize (I ltac:(rewrite Zlength_nil; lia)).
  destruct R as [R|[R|[R S]]]; [specialize (F R); lia | auto |]. subst r2.
  assert (a2ulabel s cap1 = (1, fst k2)) as H3.
  { apply (a2ulabel_fit s cap2 cap1). unfold a2ulabel. rewrite E2. auto. lia. }
  rewrite H1 in H3. inversion H3 as [H4]. rewrite H4 in H2. lia.
Qed.
