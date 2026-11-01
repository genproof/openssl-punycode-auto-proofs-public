(* Law api_a2ulabel_copy: the facts about the model that the law needs.  The harness assumes (its gp_assume loop)
   that no label of the string s starts with "xn--" in any case: at every position i with i + 3 < |s| that starts a
   label (i = 0 or s[i-1] = '.'), the octets s[i..i+3] are not x/X, n/N, '-', '-' (acp_noprefix).  Then no label is
   is_ace, ossl_a2ulabel copies every label as it is, and Model.a2ulabel writes s and its NUL when they fit in the
   capacity (result 1), else it gives 0. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.

(* The condition of the harness's gp_assume loop on the string s. *)
Definition acp_noprefix (s: list Z) : Prop :=
  forall i, 0 <= i -> i + 3 < Zlength s -> (i = 0 \/ Znth (i - 1) s = 46) ->
    ~ ((Znth i s = 120 \/ Znth i s = 88) /\ (Znth (i + 1) s = 110 \/ Znth (i + 1) s = 78) /\
       Znth (i + 2) s = 45 /\ Znth (i + 3) s = 45).

(* The labels joined back with '.' between them: the inverse of labels. *)
Fixpoint acp_joinl (ls: list (list Z)) : list Z :=
  match ls with
  | [] => []
  | l :: ls' => match ls' with [] => l | _ => l ++ 46 :: acp_joinl ls' end
  end.

Lemma acp_labels_from_cons s cur: exists l L, labels_from s cur = l :: L.
Proof.
  revert cur; induction s as [|c s IH]; intros cur; simpl.
  - eauto.
  - destruct (c =? 46); eauto.
Qed.

(* Splitting at every '.' and joining back gives the string. *)
Lemma acp_joinl_labels_from s cur: acp_joinl (labels_from s cur) = cur ++ s.
Proof.
  revert cur; induction s as [|c s IH]; intros cur; simpl.
  - rewrite app_nil_r; reflexivity.
  - destruct (c =? 46) eqn:E.
    + apply Z.eqb_eq in E; subst c.
      destruct (acp_labels_from_cons s []) as (l & L & HL).
      rewrite HL. change (acp_joinl (cur :: l :: L)) with (cur ++ 46 :: acp_joinl (l :: L)).
      rewrite <- HL, IH. reflexivity.
    + rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma acp_joinl_labels s: acp_joinl (labels s) = s.
Proof. apply acp_joinl_labels_from. Qed.

(* The first label of a string without the prefix is not ACE. *)
Lemma acp_head l t: acp_noprefix (l ++ t) -> is_ace l = false.
Proof.
  intros H. destruct (is_ace l) eqn:E; [| reflexivity]. unfold is_ace in E.
  repeat rewrite andb_true_iff in E. repeat rewrite orb_true_iff in E. repeat rewrite Z.eqb_eq in E.
  destruct E as [[[[E4 E0] E1] E2] E3]. apply Z.leb_le in E4.
  exfalso. apply (H 0); [lia | rewrite Zlength_app; pose proof (Zlength_nonneg t); lia | left; reflexivity |].
  rewrite !Znth_app1 by lia. simpl. tauto.
Qed.

(* The labels after the first '.' have no prefix either. *)
Lemma acp_tail l t: acp_noprefix (l ++ 46 :: t) -> acp_noprefix t.
Proof.
  intros H i Hi Hlen Hpos Hc.
  assert (Hs: forall j, 0 <= j -> Znth (j + Zlength l + 1) (l ++ 46 :: t) = Znth j t).
  { intros j Hj. rewrite Znth_app2 by lia.
    replace (j + Zlength l + 1 - Zlength l) with (j + 1) by lia.
    rewrite Znth_pos_cons by lia. f_equal; lia. }
  apply (H (i + Zlength l + 1)).
  - pose proof (Zlength_nonneg l); lia.
  - rewrite Zlength_app, Zlength_cons; lia.
  - right. rewrite Znth_app2 by lia.
    replace (i + Zlength l + 1 - 1 - Zlength l) with i by lia.
    destruct (Z.eq_dec i 0) as [-> | Hi0]; [reflexivity |].
    destruct Hpos as [Hpos | Hpos]; [lia |].
    rewrite Znth_pos_cons by lia. exact Hpos.
  - replace (i + Zlength l + 1 + 1) with ((i + 1) + Zlength l + 1) by lia.
    replace (i + Zlength l + 1 + 2) with ((i + 2) + Zlength l + 1) by lia.
    replace (i + Zlength l + 1 + 3) with ((i + 3) + Zlength l + 1) by lia.
    rewrite !Hs by lia. exact Hc.
Qed.

Lemma acp_nonace ls: acp_noprefix (acp_joinl ls) -> Forall (fun l => is_ace l = false) ls.
Proof.
  induction ls as [|l ls IH]; intros H; constructor.
  - destruct ls as [|l' ls'].
    + apply (acp_head l []). rewrite app_nil_r. exact H.
    + apply (acp_head l (46 :: acp_joinl (l' :: ls'))). exact H.
  - destruct ls as [|l' ls']; [constructor |].
    apply IH. apply (acp_tail l). exact H.
Qed.

(* The sink: the short flag is sticky; a write that fits is done. *)
Lemma acp_put_sticky cap k bs: snd k = true -> snd (put cap k bs) = true.
Proof.
  intros H. unfold put. destruct (Zlength bs =? 0); [exact H |].
  destruct (cap - Zlength (fst k) <? Zlength bs); [reflexivity | exact H].
Qed.

Lemma acp_put_fit cap k bs:
  snd k = false -> Zlength (fst k) + Zlength bs <= cap -> put cap k bs = (fst k ++ bs, false).
Proof.
  intros H Hc. destruct k as [o f]; simpl in *; subst f. unfold put; simpl.
  destruct (Zlength bs =? 0) eqn:E.
  - apply Z.eqb_eq, Zlength_nil_inv in E. subst bs. rewrite app_nil_r. reflexivity.
  - destruct (cap - Zlength o <? Zlength bs) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma acp_put_cases cap k bs:
  Zlength (fst k) <= cap ->
  (Zlength (fst k) + Zlength bs <= cap /\ put cap k bs = (fst k ++ bs, snd k)) \/ snd (put cap k bs) = true.
Proof.
  intros Hk. destruct k as [o f]. unfold put; simpl in *.
  destruct (Zlength bs =? 0) eqn:E.
  - apply Z.eqb_eq, Zlength_nil_inv in E. subst bs. rewrite app_nil_r, Zlength_nil.
    left; split; [lia | reflexivity].
  - destruct (cap - Zlength o <? Zlength bs) eqn:E2; [right; reflexivity |].
    apply Z.ltb_ge in E2. left; split; [lia | reflexivity].
Qed.

Lemma acp_step cap k l: is_ace l = false -> label_step cap k l = (true, put cap k l).
Proof. intros H. unfold label_step. rewrite H. reflexivity. Qed.

(* A short sink stays short: the result is 0. *)
Lemma acp_labels_short ls cap k:
  Forall (fun l => is_ace l = false) ls -> snd k = true -> fst (a2u_labels cap k ls) = 0.
Proof.
  revert k; induction ls as [|l ls IH]; intros k Hf Hk; simpl.
  - rewrite acp_put_sticky by exact Hk. reflexivity.
  - inversion Hf as [|? ? Hl Hf']; subst. rewrite acp_step by exact Hl.
    destruct ls as [|l' ls'].
    + rewrite acp_put_sticky by (repeat apply acp_put_sticky; exact Hk). reflexivity.
    + apply IH; [exact Hf' |]. rewrite acp_put_sticky by (repeat apply acp_put_sticky; exact Hk). reflexivity.
Qed.

(* The length side conditions of the two lemmas below. *)
Ltac acp_len :=
  simpl fst in *; simpl snd in *; change (acp_joinl []) with (@nil Z) in *;
  rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *; lia.

(* Everything fits: the labels joined and the NUL are written, the result is 1. *)
Lemma acp_labels_fit ls cap k:
  Forall (fun l => is_ace l = false) ls -> snd k = false ->
  Zlength (fst k) + Zlength (acp_joinl ls) + 1 <= cap ->
  a2u_labels cap k ls = (1, (fst k ++ acp_joinl ls ++ [0], false)).
Proof.
  revert k; induction ls as [|l ls IH]; intros k Hf Hk Hc; simpl.
  - rewrite (acp_put_fit cap k) by (try exact Hk; acp_len).
    reflexivity.
  - inversion Hf as [|? ? Hl Hf']; subst. rewrite acp_step by exact Hl.
    destruct ls as [|l' ls'].
    + change (acp_joinl [l]) with l in Hc. rewrite (acp_put_fit cap k) by (try exact Hk; acp_len).
      rewrite acp_put_fit by (try reflexivity; acp_len).
      simpl. rewrite <- app_assoc. reflexivity.
    + change (acp_joinl (l :: l' :: ls')) with (l ++ 46 :: acp_joinl (l' :: ls')) in *.
      pose proof (Zlength_nonneg (acp_joinl (l' :: ls'))).
      rewrite Zlength_app, Zlength_cons in Hc.
      rewrite (acp_put_fit cap k) by (try exact Hk; acp_len).
      rewrite acp_put_fit by (try reflexivity; acp_len).
      rewrite IH; [| exact Hf' | reflexivity | acp_len].
      simpl. rewrite <- !app_assoc. reflexivity.
Qed.

(* They do not fit: the result is 0. *)
Lemma acp_labels_over ls cap k:
  Forall (fun l => is_ace l = false) ls -> Zlength (fst k) <= cap ->
  cap < Zlength (fst k) + Zlength (acp_joinl ls) + 1 -> fst (a2u_labels cap k ls) = 0.
Proof.
  revert k; induction ls as [|l ls IH]; intros k Hf Hk Hc; simpl.
  - destruct (acp_put_cases cap k [0] Hk) as [[Hc' _] | Hs].
    + acp_len.
    + rewrite Hs. reflexivity.
  - inversion Hf as [|? ? Hl Hf']; subst. rewrite acp_step by exact Hl.
    destruct (acp_put_cases cap k l Hk) as [[Hc1 Hp] | Hs].
    2:{ destruct ls as [|l' ls'].
        - rewrite acp_put_sticky by exact Hs. reflexivity.
        - apply acp_labels_short; [exact Hf' | apply acp_put_sticky; exact Hs]. }
    rewrite Hp.
    destruct ls as [|l' ls'].
    + simpl in Hc. destruct (acp_put_cases cap (fst k ++ l, snd k) [0]) as [[Hc' _] | Hs];
        [acp_len | acp_len | rewrite Hs; reflexivity].
    + change (acp_joinl (l :: l' :: ls')) with (l ++ 46 :: acp_joinl (l' :: ls')) in *.
      pose proof (Zlength_nonneg (acp_joinl (l' :: ls'))).
      rewrite Zlength_app, Zlength_cons in Hc.
      destruct (acp_put_cases cap (fst k ++ l, snd k) [46]) as [[Hc2 Hp2] | Hs];
        [acp_len | | apply acp_labels_short; [exact Hf' | exact Hs]].
      rewrite Hp2. apply IH; [exact Hf' | acp_len | acp_len].
Qed.

(* The string and its NUL fit in the capacity: they are written, the result is 1; else the result is 0. *)
Lemma acp_a2ulabel s cap:
  acp_noprefix s -> 0 <= cap ->
  (Zlength s + 1 <= cap -> a2ulabel s cap = (1, s ++ [0])) /\
  (cap < Zlength s + 1 -> fst (a2ulabel s cap) = 0).
Proof.
  intros H Hcap.
  assert (Hf: Forall (fun l => is_ace l = false) (labels s)).
  { apply acp_nonace. rewrite acp_joinl_labels. exact H. }
  unfold a2ulabel. split; intros Hc.
  - rewrite acp_labels_fit; [| exact Hf | reflexivity | simpl; rewrite acp_joinl_labels, Zlength_nil; lia].
    simpl. rewrite acp_joinl_labels. reflexivity.
  - pose proof (acp_labels_over (labels s) cap ([], false) Hf) as Ho.
    simpl in Ho. rewrite acp_joinl_labels, Zlength_nil in Ho.
    destruct (a2u_labels cap ([], false) (labels s)) as [r k] eqn:E.
    simpl in *. apply Ho; lia.
Qed.

Lemma acp_a2ulabel_fits s cap:
  acp_noprefix s -> Zlength s + 1 <= cap -> a2ulabel s cap = (1, s ++ [0]).
Proof.
  intros H Hc. apply (acp_a2ulabel s cap H); [ pose proof (Zlength_nonneg s); lia | exact Hc ].
Qed.

Lemma acp_a2ulabel_short s cap:
  acp_noprefix s -> 0 <= cap -> cap < Zlength s + 1 -> fst (a2ulabel s cap) = 0.
Proof.
  intros H Hc. apply (acp_a2ulabel s cap H Hc).
Qed.
