(* Helpers of ARAce1.v (pr_a2ulabel, an ACE label: the call of pr_decode): the string cut in three parts, the
   failing label in the model, the local struct pr_dec between the a2ulabel and the decode compspecs. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

(* A string array cut into [0, a), [a, b), [b, n): each part an arr0 (emp when empty). *)
Lemma ace1_zero_emp: forall sh m (v: list val) p, isptr p -> m = 0 -> Zlength v = m ->
  data_at sh (tarray tuchar m) v p = emp.
Proof.
  intros. subst. apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_eq; auto.
Qed.

Lemma ace1_split3: forall sh n a b (l: list Z) p, 0 <= a <= b -> b <= n -> Zlength l = n -> isptr p ->
  (0 < n -> field_compatible (tarray tuchar n) [] p) ->
  arr0 sh tuchar n (vb l) p =
  arr0 sh tuchar a (vb (sublist 0 a l)) p * arr0 sh tuchar (b - a) (vb (sublist a b l)) (offset_val a p) *
  arr0 sh tuchar (n - b) (vb (sublist b n l)) (offset_val b p).
Proof.
  intros sh n a b l p Hab Hb Hl Hp Hfc. unfold arr0.
  destruct (Z.eq_dec n 0).
  { rewrite !if_true by lia. rewrite !sepcon_emp; auto. }
  assert (Hfc': field_compatible (tarray tuchar n) [] p) by (apply Hfc; lia).
  rewrite (split3_data_at_Tarray_tuchar sh n a b) by (rewrite ?Zlength_vb; lia).
  rewrite !field_address0_offset by (apply arr_field_compatible0; [auto | lia]).
  replace (nested_field_offset (tarray tuchar n) [ArraySubsc a]) with a
    by (unfold nested_field_offset; simpl; lia).
  replace (nested_field_offset (tarray tuchar n) [ArraySubsc b]) with b
    by (unfold nested_field_offset; simpl; lia).
  unfold vb. rewrite !sublist_map. fold (vb (sublist 0 a l)) (vb (sublist a b l)) (vb (sublist b n l)).
  assert (Z1: Zlength (vb (sublist 0 a l)) = a) by (rewrite Zlength_vb, Zlength_sublist; lia).
  assert (Z2: Zlength (vb (sublist a b l)) = b - a) by (rewrite Zlength_vb, Zlength_sublist; lia).
  assert (Z3: Zlength (vb (sublist b n l)) = n - b) by (rewrite Zlength_vb, Zlength_sublist; lia).
  destruct (Z.eq_dec a 0) as [Ha|Ha];
  [rewrite (ace1_zero_emp sh a) by auto | ];
  (destruct (Z.eq_dec (b - a) 0) as [Hba|Hba];
   [rewrite (ace1_zero_emp sh (b - a)) by (auto; normalize) | ]);
  (destruct (Z.eq_dec (n - b) 0) as [Hnb|Hnb];
   [rewrite (ace1_zero_emp sh (n - b)) by (auto; normalize) | ]); auto.
Qed.

(* The rest of the label after the prefix. *)
Lemma ace1_rest: forall s st, 0 <= st <= Zlength s -> 4 <= lab_end s st - st ->
  sublist 4 (Zlength (lab s st)) (lab s st) = sublist (st + 4) (lab_end s st) s.
Proof.
  intros s st H H4. pose proof (lab_end_range s st H). unfold lab.
  rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* A failing label ends the model's run with -1. *)
Lemma ace1_fail: forall s cap k st k1, 0 <= st <= Zlength s ->
  label_step cap k (lab s st) = (false, k1) ->
  a2u_labels cap k (labels (rem s st)) = (-1, k1).
Proof.
  intros s cap k st k1 H E. pose proof (lab_end_range s st H).
  destruct (Z.eq_dec (lab_end s st) (Zlength s)).
  - rewrite a2u_labels_last by auto. rewrite E. reflexivity.
  - rewrite a2u_labels_next by lia. rewrite E. reflexivity.
Qed.

Lemma ace1_a2ulabel: forall s cap r k1, A0 s cap = (r, k1) -> a2ulabel s cap = (r, fst k1).
Proof. intros. rewrite a2ulabel_eq. unfold A0 in H. rewrite H. reflexivity. Qed.

(* The struct pr_dec: the same composite under both compspecs. *)
#[export] Instance ace1_CCad : change_composite_env CS RefDec.CS. make_cs_preserve CS RefDec.CS. Defined.

Lemma ace1_dec_: forall sh p,
  @data_at_ CS sh t_decA p = @data_at_ RefDec.CS sh RefDec.t_dec p.
Proof.
  intros. apply (f_equal (fun f => f p)). apply (@data_at__change_composite CS RefDec.CS ace1_CCad). reflexivity.
Qed.

Lemma ace1_dec: forall sh (v: val * val) p,
  @data_at RefDec.CS sh RefDec.t_dec v p = @data_at CS sh t_decA v p.
Proof.
  intros. apply (f_equal (fun f => f p)). symmetry.
  apply (@data_at_change_composite CS RefDec.CS ace1_CCad); [apply JMeq_refl | reflexivity].
Qed.

Lemma ace1_cps: forall sh (v: list val) p,
  @arr0 RefDec.CS sh tuint 512 v p = @data_at CS sh (tarray tuint label_cap) v p.
Proof. intros. unfold arr0. rewrite if_false by lia. apply data_at_tuint_cs. Qed.
