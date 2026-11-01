(* Plain-Coq facts of the model used by the body of pr_a2ulabel: the labels of a string, the sink. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* The position of the first '.' of l (Zlength l when there is none). *)
Fixpoint dot_index (l: list Z) : Z :=
  match l with
  | [] => 0
  | x :: l' => if x =? 46 then 0 else 1 + dot_index l'
  end.

Lemma dot_index_range: forall l, 0 <= dot_index l <= Zlength l.
Proof.
  induction l; simpl; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons. destruct (a =? 46); lia.
Qed.

Lemma dot_index_none: forall l, dot_index l = Zlength l -> ~ In 46 l.
Proof.
  induction l; simpl; auto. rewrite Zlength_cons. intros H [E|I].
  - subst. simpl in H. pose proof (Zlength_nonneg l). lia.
  - destruct (a =? 46); [pose proof (Zlength_nonneg l); lia|]. apply IHl; auto; lia.
Qed.

Lemma dot_index_found: forall l, dot_index l < Zlength l -> Znth (dot_index l) l = 46.
Proof.
  induction l; simpl; [rewrite Zlength_nil; lia|]. rewrite Zlength_cons.
  destruct (a =? 46) eqn:E; intros H.
  - apply Z.eqb_eq in E. subst. apply Znth_0_cons.
  - pose proof (dot_index_range l). rewrite Znth_pos_cons by lia.
    replace (1 + dot_index l - 1) with (dot_index l) by lia. apply IHl; lia.
Qed.

Lemma dot_index_before: forall l i, 0 <= i < dot_index l -> Znth i l <> 46.
Proof.
  induction l; simpl; intros i H; [lia|].
  destruct (a =? 46) eqn:E; [lia|]. apply Z.eqb_neq in E.
  destruct (Z.eq_dec i 0).
  - subst. rewrite Znth_0_cons. auto.
  - rewrite Znth_pos_cons by lia. apply IHl. lia.
Qed.

(* The search loop: from a position i before the first '.', either i is the first '.' / the end, or the
   octet at i is not '.'. *)
Lemma dot_index_step: forall l i, 0 <= i <= dot_index l -> i < Zlength l -> Znth i l <> 46 -> i < dot_index l.
Proof.
  intros l i R L N. destruct (Z.eq_dec i (dot_index l)); [|lia].
  subst. exfalso. apply N. apply dot_index_found. auto.
Qed.

Lemma labels_from_none: forall s cur, ~ In 46 s -> labels_from s cur = [cur ++ s].
Proof.
  induction s; simpl; intros cur H.
  - rewrite app_nil_r. auto.
  - destruct (a =? 46) eqn:E; [apply Z.eqb_eq in E; subst; tauto|].
    rewrite IHs by tauto. rewrite <- app_assoc. auto.
Qed.

Lemma labels_from_split: forall s cur, dot_index s < Zlength s ->
  labels_from s cur = (cur ++ sublist 0 (dot_index s) s) :: labels (sublist (dot_index s + 1) (Zlength s) s).
Proof.
  induction s; simpl; intros cur H; [rewrite Zlength_nil in H; lia|].
  rewrite Zlength_cons in *.
  destruct (a =? 46) eqn:E.
  - rewrite sublist_nil, app_nil_r. rewrite sublist_1_cons.
    replace (Z.succ (Zlength s) - 1) with (Zlength s) by lia. rewrite sublist_same by lia. reflexivity.
  - pose proof (dot_index_range s).
    rewrite IHs by lia. rewrite <- app_assoc.
    rewrite sublist_0_cons by lia. rewrite sublist_S_cons by lia.
    replace (1 + dot_index s - 1) with (dot_index s) by lia.
    replace (1 + dot_index s + 1 - 1) with (dot_index s + 1) by lia.
    replace (Z.succ (Zlength s) - 1) with (Zlength s) by lia. simpl. reflexivity.
Qed.

Lemma labels_none: forall s, dot_index s = Zlength s -> labels s = [s].
Proof. intros. unfold labels. rewrite labels_from_none; auto. apply dot_index_none; auto. Qed.

Lemma labels_split: forall s, dot_index s < Zlength s ->
  labels s = sublist 0 (dot_index s) s :: labels (sublist (dot_index s + 1) (Zlength s) s).
Proof. intros. unfold labels at 1. rewrite labels_from_split; auto. Qed.

Lemma labels_from_ne: forall s cur, labels_from s cur <> [].
Proof. induction s; simpl; intros; [discriminate|]. destruct (a =? 46); [discriminate|apply IHs]. Qed.

Lemma labels_ne: forall s, labels s <> [].
Proof. intros. apply labels_from_ne. Qed.

(* The remaining string from st: its first label ends at st + dot_index. *)
Section Rem.
Variable s: list Z.

Definition rem (st: Z) : list Z := sublist st (Zlength s) s.
Definition lab_end (st: Z) : Z := st + dot_index (rem st).
Definition lab (st: Z) : list Z := sublist st (lab_end st) s.

Lemma lab_end_range: forall st, 0 <= st <= Zlength s -> st <= lab_end st <= Zlength s.
Proof.
  intros. unfold lab_end, rem. pose proof (dot_index_range (sublist st (Zlength s) s)).
  rewrite Zlength_sublist in H0 by lia. lia.
Qed.

(* The model of one step of the label loop. *)
Lemma a2u_labels_last: forall cap k st, 0 <= st <= Zlength s -> lab_end st = Zlength s ->
  a2u_labels cap k (labels (rem st)) =
  let (ok, k1) := label_step cap k (lab st) in
  if ok then let k2 := put cap k1 [0] in (if snd k2 then 0 else 1, k2) else (-1, k1).
Proof.
  intros cap k st R E. unfold lab. rewrite E. unfold lab_end in E.
  rewrite labels_none.
  - simpl. reflexivity.
  - unfold rem in *. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma a2u_labels_next: forall cap k st, 0 <= st <= Zlength s -> lab_end st < Zlength s ->
  a2u_labels cap k (labels (rem st)) =
  let (ok, k1) := label_step cap k (lab st) in
  if ok then a2u_labels cap (put cap k1 [46]) (labels (rem (lab_end st + 1))) else (-1, k1).
Proof.
  intros cap k st R E. pose proof (lab_end_range st R).
  unfold lab_end in *. unfold lab.
  assert (L: Zlength (rem st) = Zlength s - st) by (unfold rem; rewrite Zlength_sublist by lia; lia).
  rewrite labels_split by lia.
  pose proof (dot_index_range (rem st)).
  set (d := dot_index (rem st)) in *.
  replace (sublist 0 d (rem st)) with (sublist st (st + d) s)
    by (unfold rem; rewrite sublist_sublist by lia; f_equal; lia).
  replace (sublist (d + 1) (Zlength (rem st)) (rem st)) with (rem (st + d + 1))
    by (rewrite L; unfold rem at 2; rewrite sublist_sublist by lia; unfold rem; f_equal; lia).
  change (lab_end st) with (st + d).
  simpl. destruct (label_step cap k _) as [ok k1]. destruct ok; auto.
  destruct (labels (rem (st + d + 1))) eqn:LL; auto.
  exfalso. eapply labels_ne; eauto.
Qed.

End Rem.

Lemma a2ulabel_eq: forall s cap,
  a2ulabel s cap = (fst (a2u_labels cap ([], false) (labels s)), fst (snd (a2u_labels cap ([], false) (labels s)))).
Proof. intros. unfold a2ulabel. destruct (a2u_labels _ _ _); reflexivity. Qed.

Lemma rem_0: forall s, rem s 0 = s.
Proof. intros. unfold rem. apply sublist_same; lia. Qed.

(* ---------------------------------------------------------------------- *)
(* The sink                                                               *)
(* ---------------------------------------------------------------------- *)

Definition sink_ok (cap: Z) (k: sink) : Prop := Zlength (fst k) <= cap /\ bytes_ok (fst k).

Lemma put_ok: forall cap k l, sink_ok cap k -> bytes_ok l -> sink_ok cap (put cap k l).
Proof.
  intros cap [w sh] l [L B] BL. unfold put, sink_ok in *; simpl in *.
  destruct (Zlength l =? 0); simpl; [auto|].
  destruct (cap - Zlength w <? Zlength l) eqn:E; simpl; [auto|].
  apply Z.ltb_ge in E. split; [rewrite Zlength_app; lia|]. apply Forall_app; auto.
Qed.

Lemma utf8_bytes: forall c, 0 <= c -> bytes_ok (utf8 c).
Proof.
  intros c H. unfold utf8, bytes_ok.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:?; [|] end;
  repeat match goal with H: (_ <? _) = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end;
  repeat match goal with H: (_ <=? _) = _ |- _ => first [apply Z.leb_le in H | apply Z.leb_gt in H] end;
  repeat constructor; change Byte.max_unsigned with 255.
  all: Z.to_euclidean_division_equations; lia.
Qed.

Lemma utf8_len: forall c, 0 <= Zlength (utf8 c) <= 4.
Proof.
  intros c. unfold utf8.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; cbv; split; congruence.
Qed.

Lemma put_utf8s_ok: forall cap cps k, sink_ok cap k -> Forall (fun c => 0 <= c) cps ->
  sink_ok cap (snd (put_utf8s cap k cps)).
Proof.
  induction cps; intros k K F; simpl; auto. inversion F; subst.
  destruct (Zlength (utf8 a) =? 0); simpl; auto.
  apply IHcps; auto. apply put_ok; auto. apply utf8_bytes; auto.
Qed.

Lemma put_utf8s_next: forall cap k cps i n, 0 <= i < n -> n <= Zlength cps ->
  put_utf8s cap k (sublist i n cps) =
  if Zlength (utf8 (Znth i cps)) =? 0 then (false, k)
  else put_utf8s cap (put cap k (utf8 (Znth i cps))) (sublist (i + 1) n cps).
Proof. intros. rewrite (sublist_next i n) by lia. reflexivity. Qed.
