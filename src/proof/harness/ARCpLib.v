(* Helpers of ARCp.v (the code-point loop of pr_a2ulabel): the model facts of an ACE label, the split of the local
   u[4] into the first n octets (written by pr_utf8) and the rest. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

Lemma cp_rest: forall s st, 0 <= st <= Zlength s -> 4 <= lab_end s st - st ->
  sublist 4 (Zlength (lab s st)) (lab s st) = sublist (st + 4) (lab_end s st) s.
Proof.
  intros s st H H4. pose proof (lab_end_range s st H). unfold lab.
  rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* A failing label ends the model's run with -1. *)
Lemma cp_fail: forall s cap k st k1, 0 <= st <= Zlength s ->
  label_step cap k (lab s st) = (false, k1) ->
  a2u_labels cap k (labels (rem s st)) = (-1, k1).
Proof.
  intros s cap k st k1 H E. pose proof (lab_end_range s st H).
  destruct (Z.eq_dec (lab_end s st) (Zlength s)).
  - rewrite a2u_labels_last by auto. rewrite E. reflexivity.
  - rewrite a2u_labels_next by lia. rewrite E. reflexivity.
Qed.

Lemma cp_a2ulabel: forall s cap r k1, A0 s cap = (r, k1) -> a2ulabel s cap = (r, fst k1).
Proof. intros. rewrite a2ulabel_eq. unfold A0 in H. rewrite H. reflexivity. Qed.

(* The label step of an ACE label decoded into cps. *)
Lemma cp_step: forall s st cap k cps, 0 <= st <= Zlength s -> is_ace (lab s st) = true ->
  Zlength (sublist (st + 4) (lab_end s st) s) < maxint ->
  decode (sublist (st + 4) (lab_end s st) s) label_cap = (true, cps) ->
  label_step cap k (lab s st) = put_utf8s cap k cps.
Proof.
  intros s st cap k cps Hst Hace Hlen Hdec.
  pose proof (lab_end_range s st Hst) as He.
  assert (Hll: Zlength (lab s st) = lab_end s st - st) by (unfold lab; rewrite Zlength_sublist; lia).
  assert (H4: 4 <= lab_end s st - st).
  { unfold is_ace in Hace. rewrite <- Hll. destruct (4 <=? Zlength (lab s st)) eqn:E; [lia | discriminate]. }
  unfold label_step. rewrite Hace, (cp_rest s st Hst H4).
  replace (maxint <=? _) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hdec. reflexivity.
Qed.

Lemma put_utf8s_last: forall cap k cps j, 0 <= j < Zlength cps -> Zlength (utf8 (Znth j cps)) <> 0 ->
  put_utf8s cap k (sublist j (Zlength cps) cps) =
  put_utf8s cap (put cap k (utf8 (Znth j cps))) (sublist (j + 1) (Zlength cps) cps).
Proof.
  intros. rewrite put_utf8s_next by lia. destruct (Zlength (utf8 (Znth j cps)) =? 0) eqn:E; auto. lia.
Qed.

Lemma put_utf8s_stop: forall cap k cps j, 0 <= j < Zlength cps -> Zlength (utf8 (Znth j cps)) = 0 ->
  put_utf8s cap k (sublist j (Zlength cps) cps) = (false, k).
Proof. intros. rewrite put_utf8s_next by lia. rewrite H0. reflexivity. Qed.

(* The local u[4]: the first n octets, then the rest. *)
Definition u_rest (n: Z) (p: val) : mpred :=
  if Z.eq_dec n 0 then data_at_ Tsh (tarray tuchar 4) p
  else data_at_ Tsh (tarray tuchar (4 - n)) (field_address0 (tarray tuchar 4) [ArraySubsc n] p).

Lemma u_split: forall n p, 0 <= n <= 4 ->
  data_at_ Tsh (tarray tuchar 4) p |-- arr0 Tsh tuchar n (Zrepeat Vundef n) p * u_rest n p.
Proof.
  intros n p H. unfold arr0, u_rest. destruct (Z.eq_dec n 0).
  - rewrite emp_sepcon. apply derives_refl.
  - rewrite !data_at__eq. unfold tarray. rewrite (split2_data_at_Tarray_tuchar Tsh 4 n) by (auto; reflexivity).
    apply sepcon_derives; apply derives_refl'; f_equal;
      [change (default_val (Tarray tuchar 4 noattr)) with (Zrepeat Vundef 4); list_solve
      | change (default_val (Tarray tuchar 4 noattr)) with (Zrepeat Vundef 4);
        change (default_val (Tarray tuchar (4 - n) noattr)) with (Zrepeat (default_val tuchar) (4 - n)); list_solve].
Qed.

Lemma u_join: forall l p, Zlength l <= 4 ->
  arr0 Tsh tuchar (Zlength l) (vb l) p * u_rest (Zlength l) p |-- data_at_ Tsh (tarray tuchar 4) p.
Proof.
  intros l p H. pose proof (Zlength_nonneg l). unfold arr0, u_rest. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon. apply derives_refl.
  - unfold tarray.
    eapply derives_trans; [ | apply (data_at_data_at_ Tsh (Tarray tuchar 4 noattr) (vb l ++ Zrepeat Vundef (4 - Zlength l)))].
    rewrite (split2_data_at_Tarray_tuchar Tsh 4 (Zlength l)) by (unfold vb; try rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
    assert (Hv: Zlength (vb l) = Zlength l) by (unfold vb; rewrite Zlength_map; auto).
    rewrite sublist_app1, sublist_app2 by lia. rewrite Hv, sublist_same by lia.
    rewrite Z.sub_diag, sublist_same by (rewrite ?Zlength_Zrepeat; lia).
    apply derives_refl.
Qed.
