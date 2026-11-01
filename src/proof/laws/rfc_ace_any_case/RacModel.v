(* The model facts behind law rfc_ace_any_case: the string an array holds up to its first NUL, and the conversion
   Model.a2ulabel of a string that starts with the ACE prefix in any case ("xn--", "Xn--", "xN--", "XN--") is the one
   of the same string with the lowercase prefix (is_ace accepts both cases, and the label is read from its fifth
   octet on). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.

(* The number of octets of l before its first 0 (all of l if none). *)
Fixpoint nul_len (l: list Z) : Z :=
  match l with [] => 0 | c :: l' => if c =? 0 then 0 else 1 + nul_len l' end.

Lemma nul_len_range l: 0 <= nul_len l <= Zlength l.
Proof.
  induction l as [ | c l IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (c =? 0); lia.
Qed.

Lemma nul_len_nonzero l: Forall (fun c => c <> 0) (sublist 0 (nul_len l) l).
Proof.
  induction l as [ | c l IH]; simpl; [ constructor | ].
  destruct (c =? 0) eqn:E; [ rewrite sublist_nil'; [ constructor | lia ] | ].
  pose proof (nul_len_range l).
  rewrite sublist_0_cons by lia. replace (1 + nul_len l - 1) with (nul_len l) by lia.
  constructor; [ apply Z.eqb_neq; auto | auto ].
Qed.

Lemma nul_len_at l: nul_len l < Zlength l -> Znth (nul_len l) l = 0.
Proof.
  induction l as [ | c l IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (c =? 0) eqn:E.
  - intros _. rewrite Znth_0_cons. apply Z.eqb_eq; auto.
  - intros H. pose proof (nul_len_range l). rewrite Znth_pos_cons by lia.
    replace (1 + nul_len l - 1) with (nul_len l) by lia. apply IH. lia.
Qed.

Lemma nul_len_app_nonzero a l: Forall (fun c => c <> 0) a -> nul_len (a ++ l) = Zlength a + nul_len l.
Proof.
  induction 1 as [ | c a Hc Ha IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. rewrite (proj2 (Z.eqb_neq c 0) Hc). lia.
Qed.

(* The string of an array that starts with four nonzero octets a: a, then the string of the rest. *)
Lemma nul_str_prefix a l: Forall (fun c => c <> 0) a ->
  sublist 0 (nul_len (a ++ l)) (a ++ l) = a ++ sublist 0 (nul_len l) l.
Proof.
  intros Ha. rewrite nul_len_app_nonzero by auto. pose proof (nul_len_range l).
  list_solve.
Qed.

(* Splitting at '.': a prefix of the current label goes to the first label. *)
Lemma labels_from_prefix s: forall q cur,
  labels_from s (q ++ cur) =
  match labels_from s cur with l :: ls => (q ++ l) :: ls | [] => [] end.
Proof.
  induction s as [ | c s IH]; intros q cur; simpl; [ reflexivity | ].
  destruct (c =? 46); [ reflexivity | ]. rewrite <- app_assoc. apply IH.
Qed.

Lemma labels_from_cons s cur: exists l ls, labels_from s cur = l :: ls.
Proof.
  revert cur. induction s as [ | c s IH]; intros cur; simpl; [ eauto | ].
  destruct (c =? 46); eauto.
Qed.

Lemma labels_from_start s q:
  labels_from s q = match labels_from s [] with l :: ls => (q ++ l) :: ls | [] => [] end.
Proof. rewrite <- (app_nil_r q) at 1. apply labels_from_prefix. Qed.

(* The first label in any case of the ACE prefix and in lowercase: label_step does not see the difference. *)
Lemma rac_label_step a b l cap k:
  (a = 88 \/ a = 120) -> (b = 78 \/ b = 110) ->
  label_step cap k ([a; b; 45; 45] ++ l) = label_step cap k ([120; 110; 45; 45] ++ l).
Proof.
  intros Ha Hb. unfold label_step.
  assert (Hace: forall x y, (x = 88 \/ x = 120) -> (y = 78 \/ y = 110) -> is_ace ([x; y; 45; 45] ++ l) = true).
  { intros x y Hx Hy. unfold is_ace. rewrite Zlength_app. change (Zlength [x; y; 45; 45]) with 4.
    rewrite !Znth_app1 by (change (Zlength [x; y; 45; 45]) with 4; lia).
    assert (4 <=? 4 + Zlength l = true) by (apply Z.leb_le; pose proof (Zlength_nonneg l); lia).
    rewrite H. destruct Hx, Hy; subst; reflexivity. }
  rewrite !Hace by auto.
  rewrite !sublist_app2 by (change (Zlength [a; b; 45; 45]) with 4 || change (Zlength [120; 110; 45; 45]) with 4;
    rewrite ?Zlength_app; change (Zlength [a; b; 45; 45]) with 4 || change (Zlength [120; 110; 45; 45]) with 4; lia).
  rewrite !Zlength_app. reflexivity.
Qed.

(* The ACE prefix in any case and the lowercase one give the same conversion. *)
Lemma rac_a2ulabel a b t cap:
  (a = 88 \/ a = 120) -> (b = 78 \/ b = 110) ->
  a2ulabel ([a; b; 45; 45] ++ t) cap = a2ulabel ([120; 110; 45; 45] ++ t) cap.
Proof.
  intros Ha Hb. unfold a2ulabel, labels.
  assert (E: forall x y, (x = 88 \/ x = 120) -> (y = 78 \/ y = 110) ->
             labels_from ([x; y; 45; 45] ++ t) [] = labels_from t [x; y; 45; 45]).
  { intros x y Hx Hy. destruct Hx, Hy; subst; reflexivity. }
  rewrite !E by auto. rewrite !(labels_from_start t [_; _; 45; 45]).
  destruct (labels_from_cons t []) as [l [ls El]]. rewrite El.
  pose proof (rac_label_step a b l cap ([], false) Ha Hb) as Hs. simpl app in Hs.
  simpl a2u_labels. rewrite Hs. reflexivity.
Qed.
