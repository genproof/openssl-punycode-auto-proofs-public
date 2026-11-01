(* Plain-Coq facts of the model used by the body of ossl_a2ulabel: the labels of a string, the ACE-prefix test of
   OPENSSL_strncasecmp, the sink. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Import ListNotations.
Local Open Scope Z_scope.

Lemma index_of_range: forall c l, 0 <= index_of c l <= Zlength l.
Proof.
  induction l; simpl; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons. destruct (a =? c); lia.
Qed.

Lemma index_of_none: forall c l, index_of c l = Zlength l -> ~ In c l.
Proof.
  induction l; simpl; auto. rewrite Zlength_cons. intros H [E|I].
  - subst. rewrite Z.eqb_refl in H. pose proof (Zlength_nonneg l). lia.
  - destruct (a =? c); [pose proof (Zlength_nonneg l); lia|]. apply IHl; auto; lia.
Qed.

Lemma index_of_found: forall c l, index_of c l < Zlength l -> Znth (index_of c l) l = c.
Proof.
  induction l; simpl; [rewrite Zlength_nil; lia|]. rewrite Zlength_cons.
  destruct (a =? c) eqn:E; intros H.
  - apply Z.eqb_eq in E. subst. apply Znth_0_cons.
  - pose proof (index_of_range c l). rewrite Znth_pos_cons by lia.
    replace (1 + index_of c l - 1) with (index_of c l) by lia. apply IHl; lia.
Qed.

Lemma index_of_before: forall c l i, 0 <= i < index_of c l -> Znth i l <> c.
Proof.
  induction l; simpl; intros i H; [lia|].
  destruct (a =? c) eqn:E; [lia|]. apply Z.eqb_neq in E.
  destruct (Z.eq_dec i 0).
  - subst. rewrite Znth_0_cons. auto.
  - rewrite Znth_pos_cons by lia. apply IHl. lia.
Qed.

(* The labels of a string: the part up to the first '.', then the labels of the rest. *)
Lemma labels_from_none: forall s cur, ~ In 46 s -> labels_from s cur = [cur ++ s].
Proof.
  induction s; simpl; intros cur H.
  - rewrite app_nil_r. auto.
  - destruct (a =? 46) eqn:E; [apply Z.eqb_eq in E; subst; tauto|].
    rewrite IHs by tauto. rewrite <- app_assoc. auto.
Qed.

Lemma labels_from_split: forall s cur, index_of 46 s < Zlength s ->
  labels_from s cur = (cur ++ sublist 0 (index_of 46 s) s) :: labels (sublist (index_of 46 s + 1) (Zlength s) s).
Proof.
  induction s; simpl; intros cur H; [rewrite Zlength_nil in H; lia|].
  rewrite Zlength_cons in *.
  destruct (a =? 46) eqn:E.
  - rewrite sublist_nil, app_nil_r. rewrite sublist_1_cons.
    replace (Z.succ (Zlength s) - 1) with (Zlength s) by lia. rewrite sublist_same by lia. reflexivity.
  - pose proof (index_of_range 46 s).
    rewrite IHs by lia. rewrite <- app_assoc.
    rewrite sublist_0_cons by lia. rewrite sublist_S_cons by lia.
    replace (1 + index_of 46 s - 1) with (index_of 46 s) by lia.
    replace (1 + index_of 46 s + 1 - 1) with (index_of 46 s + 1) by lia.
    replace (Z.succ (Zlength s) - 1) with (Zlength s) by lia. simpl. reflexivity.
Qed.

Lemma labels_none: forall s, index_of 46 s = Zlength s -> labels s = [s].
Proof. intros. unfold labels. rewrite labels_from_none; auto. apply index_of_none; auto. Qed.

Lemma labels_split: forall s, index_of 46 s < Zlength s ->
  labels s = sublist 0 (index_of 46 s) s :: labels (sublist (index_of 46 s + 1) (Zlength s) s).
Proof. intros. unfold labels at 1. rewrite labels_from_split; auto. Qed.

(* The label at the start of a string. *)
Definition label_of (s: list Z) : list Z := sublist 0 (index_of 46 s) s.

(* ---------------------------------------------------------------------- *)
(* The ACE prefix: OPENSSL_strncasecmp(s, "xn--", 4) == 0                  *)
(* ---------------------------------------------------------------------- *)

Definition is_x (a: Z) : bool := (a =? 120) || (a =? 88).
Definition is_n (a: Z) : bool := (a =? 110) || (a =? 78).

Ltac zcases :=
  repeat match goal with
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
  end; simpl in *; try reflexivity; try lia.

Lemma tl_x: forall a, 1 <= a <= 255 -> (tolower (sbyte a) - tolower (sbyte 120) =? 0) = is_x a.
Proof. intros a H. unfold tolower, sbyte, is_x. simpl. zcases. Qed.

Lemma tl_n: forall a, 1 <= a <= 255 -> (tolower (sbyte a) - tolower (sbyte 110) =? 0) = is_n a.
Proof. intros a H. unfold tolower, sbyte, is_n. simpl. zcases. Qed.

Lemma tl_dash: forall a, 1 <= a <= 255 -> (tolower (sbyte a) - tolower (sbyte 45) =? 0) = (a =? 45).
Proof. intros a H. unfold tolower, sbyte. simpl. zcases. Qed.

Lemma ncasecmp_step0: forall a r b r' n, 1 <= a <= 255 ->
  (ncasecmp (a :: r) (b :: r') (S n) =? 0) =
  (tolower (sbyte a) - tolower (sbyte b) =? 0) && (ncasecmp r r' n =? 0).
Proof.
  intros. simpl. replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  remember (tolower (sbyte a) - tolower (sbyte b)) as t.
  destruct (t =? 0) eqn:E; simpl; auto.
Qed.

Definition pref4 (s: list Z) : bool :=
  (4 <=? Zlength s) && is_x (Znth 0 s) && is_n (Znth 1 s) && (Znth 2 s =? 45) && (Znth 3 s =? 45).

Lemma ncasecmp_pref4: forall s, str_ok s ->
  (ncasecmp (s ++ [0]) ([120; 110; 45; 45] ++ [0]) 4 =? 0) = pref4 s.
Proof.
  intros s OK. unfold pref4.
  destruct s as [|a [|b [|c [|d r]]]]; simpl app;
    repeat match goal with H: str_ok (_ :: _) |- _ => inversion H; subst; clear H end;
    repeat match goal with H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H end;
    change Byte.max_unsigned with 255 in *;
    change 4%nat with (S (S (S (S O))));
    repeat (rewrite ncasecmp_step0 by lia);
    try rewrite tl_x by lia; try rewrite tl_n by lia; try rewrite !tl_dash by lia;
    rewrite ?Zlength_cons, ?Zlength_nil; simpl; rewrite ?andb_false_r; auto.
  unfold Znth; simpl. rewrite ?andb_true_r.
  replace (4 <=? Z.succ (Z.succ (Z.succ (Z.succ (Zlength r))))) with true
    by (symmetry; apply Z.leb_le; pose proof (Zlength_nonneg r); lia).
  simpl. rewrite !andb_assoc. destruct (r ++ [0]); simpl; rewrite andb_true_r; auto.
Qed.

Lemma Zlength_label_of: forall s, Zlength (label_of s) = index_of 46 s.
Proof. intros. unfold label_of. pose proof (index_of_range 46 s). rewrite Zlength_sublist; lia. Qed.

Lemma is_ace_pref4: forall s, is_ace (label_of s) = pref4 s.
Proof.
  intros s. pose proof (index_of_range 46 s) as R. unfold is_ace, pref4.
  rewrite Zlength_label_of.
  destruct (Z_lt_le_dec (index_of 46 s) 4) as [L|L].
  - replace (4 <=? index_of 46 s) with false by (symmetry; apply Z.leb_gt; lia). simpl.
    destruct (4 <=? Zlength s) eqn:E; simpl; auto. apply Z.leb_le in E.
    pose proof (index_of_found 46 s ltac:(lia)) as F.
    assert (index_of 46 s = 0 \/ index_of 46 s = 1 \/ index_of 46 s = 2 \/ index_of 46 s = 3) as C by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C in F; rewrite F;
      destruct (is_x (Znth 0 s)), (is_n (Znth 1 s)), (Znth 2 s =? 45); simpl; auto.
  - unfold label_of. rewrite !Znth_sublist by lia. simpl.
    replace (4 <=? index_of 46 s) with true by (symmetry; apply Z.leb_le; lia).
    replace (4 <=? Zlength s) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* The test of the C code (on the remaining string s with its NUL) is the model's is_ace of the label. *)
Lemma ace_test: forall s, str_ok s ->
  (ncasecmp (s ++ [0]) ([120; 110; 45; 45] ++ [0]) 4 =? 0) = is_ace (label_of s).
Proof. intros. rewrite is_ace_pref4. apply ncasecmp_pref4; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* The sink                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma put_split: forall cap w sh l,
  put cap (w, sh) l = (fst (put cap (w, false) l), sh || negb (OpensslPunycode.proof.packet.PacketSpec.put_ok cap w l)).
Proof.
  intros. unfold put, OpensslPunycode.proof.packet.PacketSpec.put_ok. simpl.
  destruct (Zlength l =? 0); simpl; [rewrite orb_false_r; auto|].
  destruct (cap - Zlength w <? Zlength l) eqn:E.
  - apply Z.ltb_lt in E. replace (Zlength l <=? cap - Zlength w) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite orb_true_r. auto.
  - apply Z.ltb_ge in E. replace (Zlength l <=? cap - Zlength w) with true by (symmetry; apply Z.leb_le; lia).
    rewrite orb_false_r. auto.
Qed.

Lemma tl_range: forall c, 0 <= c <= 255 -> -128 <= tolower (sbyte c) <= 159.
Proof. intros c H. unfold tolower, sbyte. zcases. Qed.

Lemma ncasecmp_range: forall n l1 l2, bytes_ok l1 -> bytes_ok l2 -> -512 <= ncasecmp l1 l2 n <= 512.
Proof.
  induction n; intros l1 l2 B1 B2; [destruct l1, l2; simpl; lia|].
  destruct l1 as [|c1 r1]; [simpl; lia|]. destruct l2 as [|c2 r2]; [simpl; lia|].
  inversion B1; inversion B2; subst. change Byte.max_unsigned with 255 in *.
  pose proof (tl_range c1 ltac:(lia)). pose proof (tl_range c2 ltac:(lia)).
  simpl. destruct (_ =? 0); simpl; [destruct (c1 =? 0); [lia | apply IHn; auto] | lia].
Qed.

Lemma labels_from_ne: forall s cur, labels_from s cur <> [].
Proof. induction s; simpl; intros; [discriminate|]. destruct (a =? 46); [discriminate|apply IHs]. Qed.

Lemma labels_ne: forall s, labels s <> [].
Proof. intros. apply labels_from_ne. Qed.

Lemma put_utf8s_next: forall cap k cps i n, 0 <= i < n -> n <= Zlength cps ->
  put_utf8s cap k (sublist i n cps) =
  if Zlength (utf8 (Znth i cps)) =? 0 then (false, k)
  else put_utf8s cap (put cap k (utf8 (Znth i cps))) (sublist (i + 1) n cps).
Proof. intros. rewrite (sublist_next i n) by lia. reflexivity. Qed.
