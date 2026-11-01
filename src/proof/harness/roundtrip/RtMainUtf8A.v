(* Helpers for MainUtf8.v (the UTF-8 loop of roundtrip's main): lengths of the UTF-8 forms, and the split of the
   buffer want around the slot pr_utf8 writes. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.
Local Open Scope logic.

Lemma utf8_len: forall c, 0 <= c <= 1114111 -> 1 <= Zlength (utf8 c) <= 4.
Proof.
  intros c Hc.
  cut (Zlength (utf8 c) = 1 \/ Zlength (utf8 c) = 2 \/ Zlength (utf8 c) = 3 \/ Zlength (utf8 c) = 4); [lia|].
  unfold utf8.
  destruct (c <? 128); [auto|].
  destruct (c <? 2048); [auto|].
  destruct (c <? 65536); [auto|].
  rewrite (proj2 (Z.leb_le c 1114111)) by lia. auto.
Qed.

Lemma utf8s_app: forall l1 l2, utf8s (l1 ++ l2) = utf8s l1 ++ utf8s l2.
Proof. intros. unfold utf8s. rewrite map_app, concat_app. auto. Qed.

Lemma utf8s_one: forall c, utf8s [c] = utf8 c.
Proof. intros. unfold utf8s. simpl. rewrite app_nil_r. auto. Qed.

Lemma utf8s_step: forall cps j, 0 <= j < Zlength cps ->
  utf8s (sublist 0 (j + 1) cps) = utf8s (sublist 0 j cps) ++ utf8 (Znth j cps).
Proof.
  intros. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite utf8s_app.
  rewrite sublist_len_1 by lia. rewrite utf8s_one. auto.
Qed.

Lemma utf8s_len_bound: forall cps, Forall (fun c => 0 <= c <= 1114111) cps ->
  0 <= Zlength (utf8s cps) <= 4 * Zlength cps.
Proof.
  induction cps; intros H.
  - unfold utf8s; simpl. rewrite Zlength_nil. lia.
  - inv H. change (a :: cps) with ([a] ++ cps). rewrite utf8s_app, Zlength_app, utf8s_one.
    specialize (IHcps H3). pose proof (utf8_len a H2). rewrite Zlength_app. change (Zlength [a]) with 1. lia.
Qed.

Lemma utf8s_prefix_len: forall cps j, 0 <= j <= Zlength cps ->
  Zlength (utf8s (sublist 0 j cps)) <= Zlength (utf8s cps).
Proof.
  intros. rewrite <- (sublist_same 0 (Zlength cps) cps) at 2 by auto.
  rewrite (sublist_split 0 j (Zlength cps)) by lia. rewrite utf8s_app, Zlength_app.
  pose proof (Zlength_nonneg (utf8s (sublist j (Zlength cps) cps))). lia.
Qed.

Lemma utf8s_step_len: forall cps j, 0 <= j < Zlength cps ->
  Zlength (utf8s (sublist 0 j cps)) + Zlength (utf8 (Znth j cps)) <= Zlength (utf8s cps).
Proof.
  intros. rewrite <- Zlength_app, <- utf8s_step by auto. apply utf8s_prefix_len. lia.
Qed.

Lemma split_want {cs cs2: compspecs}: forall sh n a k (A: list val) p,
  0 <= a -> 0 < k -> a + k <= n -> Zlength A = a ->
  @data_at cs sh (tarray tuchar n) (A ++ Zrepeat Vundef (n - a)) p |--
  !! @field_compatible cs (tarray tuchar n) [] p &&
  (@data_at cs sh (tarray tuchar a) A p *
   @arr0 cs2 sh tuchar k (Zrepeat Vundef k) (offset_val a p) *
   @data_at cs sh (tarray tuchar (n - a - k)) (Zrepeat Vundef (n - a - k)) (offset_val (a + k) p)).
Proof.
  intros. assert_PROP (@field_compatible cs (tarray tuchar n) [] p) by (saturate_local; apply prop_right; auto).
  apply andp_right; [apply prop_right; auto|].
  unfold arr0. rewrite if_false by lia.
  rewrite (data_at_tuchar_cs cs2 cs).
  replace (Zrepeat Vundef (n - a)) with (Zrepeat Vundef k ++ Zrepeat Vundef (n - a - k)).
  2: rewrite Zrepeat_app by lia; f_equal; lia.
  rewrite (split2_data_at_Tarray_app a n) by list_solve.
  rewrite (split2_data_at_Tarray_app k (n - a)) by list_solve.
  rewrite field_address0_SUB_SUB by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite <- sepcon_assoc.
  replace (0 + 1 * (k + a)) with (a + k) by lia. replace (0 + 1 * a) with a by lia. auto.
Qed.

Lemma join_want {cs cs2: compspecs}: forall sh n a k (A B: list val) p,
  0 <= a -> 0 < k -> a + k <= n -> Zlength A = a -> Zlength B = k ->
  @field_compatible cs (tarray tuchar n) [] p ->
  @data_at cs sh (tarray tuchar a) A p *
  @arr0 cs2 sh tuchar k B (offset_val a p) *
  @data_at cs sh (tarray tuchar (n - a - k)) (Zrepeat Vundef (n - a - k)) (offset_val (a + k) p) |--
  @data_at cs sh (tarray tuchar n) ((A ++ B) ++ Zrepeat Vundef (n - (a + k))) p.
Proof.
  intros.
  unfold arr0. rewrite if_false by lia.
  rewrite (data_at_tuchar_cs cs2 cs).
  rewrite <- app_assoc. replace (n - (a + k)) with (n - a - k) by lia.
  rewrite (split2_data_at_Tarray_app a n) by list_solve.
  rewrite (split2_data_at_Tarray_app k (n - a)) by list_solve.
  rewrite field_address0_SUB_SUB by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite <- sepcon_assoc.
  replace (0 + 1 * (k + a)) with (a + k) by lia. replace (0 + 1 * a) with a by lia. auto.
Qed.
