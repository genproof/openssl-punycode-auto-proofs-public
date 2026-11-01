(* Helpers of MainLoop1.v (the loop that picks the code points of harness/x_roundtrip.c): the slot j of the
   unsigned int array cps as the 4 octets pick() writes, and back. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.
Local Open Scope logic.

Section Slot.
Context {cs: compspecs}.

(* Element |a| of a tuint array, as the tuchar[4] that nondet_bytes fills. *)
Lemma slot_split: forall sh m (a b: list val) (x: val) p,
  Zlength a + 1 + Zlength b = m ->
  data_at sh (tarray tuint m) (a ++ [x] ++ b) p |--
  !! (field_compatible (tarray tuint m) [] p /\ field_compatible tuint [] (offset_val (4 * Zlength a) p)) &&
  (data_at sh (tarray tuint (Zlength a)) a p * data_at_ sh (tarray tuchar 4) (offset_val (4 * Zlength a) p) *
   data_at sh (tarray tuint (Zlength b)) b (offset_val (4 * (Zlength a + 1)) p)).
Proof.
  intros sh m a b x p Hm.
  assert_PROP (field_compatible (tarray tuint m) [] p) as FC by entailer!.
  pose proof (Zlength_nonneg a). pose proof (Zlength_nonneg b).
  rewrite (split2_data_at_Tarray_app (Zlength a) m sh tuint a ([x] ++ b)) by (auto; autorewrite with sublist; lia).
  rewrite arr_field_address0 by (auto; lia).
  assert_PROP (field_compatible (tarray tuint (m - Zlength a)) [] (offset_val (sizeof tuint * Zlength a) p))
    as FC1 by entailer!.
  rewrite (split2_data_at_Tarray_app 1 (m - Zlength a) sh tuint [x] b) by list_solve.
  rewrite arr_field_address0 by (auto; lia).
  rewrite (data_at_singleton_array_eq sh tuint x [x]) by auto.
  rewrite offset_offset_val.
  replace (sizeof tuint * Zlength a)%Z with (4 * Zlength a)%Z by (simpl; lia).
  replace (4 * Zlength a + sizeof tuint * 1)%Z with (4 * (Zlength a + 1))%Z by (simpl; lia).
  replace (m - Zlength a - 1) with (Zlength b) by lia.
  sep_apply (data_at_data_at_ sh tuint x).
  assert_PROP (field_compatible tuint [] (offset_val (4 * Zlength a) p)) as FCx by entailer!.
  sep_apply (data_at__memory_block_cancel sh tuint (offset_val (4 * Zlength a) p)).
  sep_apply (memory_block_data_at__tarray_tuchar sh (offset_val (4 * Zlength a) p) (sizeof tuint)
               ltac:(simpl; rep_lia)).
  entailer!.
Qed.

(* And back: the element written. *)
Lemma slot_join: forall sh m (a b: list val) (v: val) p,
  Zlength a + 1 + Zlength b = m ->
  field_compatible (tarray tuint m) [] p ->
  data_at sh (tarray tuint (Zlength a)) a p * data_at sh tuint v (offset_val (4 * Zlength a) p) *
  data_at sh (tarray tuint (Zlength b)) b (offset_val (4 * (Zlength a + 1)) p) |--
  data_at sh (tarray tuint m) (a ++ [v] ++ b) p.
Proof.
  intros sh m a b v p Hm FC.
  pose proof (Zlength_nonneg a). pose proof (Zlength_nonneg b).
  pose proof FC as FC'.
  rewrite (field_compatible_Tarray_split tuint (Zlength a) m p) in FC' by lia.
  destruct FC' as [_ FC1].
  rewrite arr_field_address0 in FC1 by (auto; lia).
  rewrite (split2_data_at_Tarray_app (Zlength a) m sh tuint a ([v] ++ b)) by list_solve.
  rewrite arr_field_address0 by (auto; lia).
  rewrite (split2_data_at_Tarray_app 1 (m - Zlength a) sh tuint [v] b) by list_solve.
  rewrite arr_field_address0 by (auto; lia).
  rewrite (data_at_singleton_array_eq sh tuint v [v]) by auto.
  rewrite offset_offset_val.
  replace (sizeof tuint * Zlength a)%Z with (4 * Zlength a)%Z by (simpl; lia).
  replace (4 * Zlength a + sizeof tuint * 1)%Z with (4 * (Zlength a + 1))%Z by (simpl; lia).
  replace (m - Zlength a - 1) with (Zlength b) by lia.
  cancel.
Qed.

(* The same with the lengths named. *)
Lemma slot_split_k: forall sh m k r (a b: list val) (x: val) p,
  Zlength a = k -> Zlength b = r -> k + 1 + r = m ->
  data_at sh (tarray tuint m) (a ++ [x] ++ b) p |--
  !! (field_compatible (tarray tuint m) [] p /\ field_compatible tuint [] (offset_val (4 * k) p)) &&
  (data_at sh (tarray tuint k) a p * data_at_ sh (tarray tuchar 4) (offset_val (4 * k) p) *
   data_at sh (tarray tuint r) b (offset_val (4 * (k + 1)) p)).
Proof. intros. subst. apply slot_split; auto. Qed.

Lemma slot_join_k: forall sh m k r (a b: list val) (v: val) p,
  Zlength a = k -> Zlength b = r -> k + 1 + r = m ->
  field_compatible (tarray tuint m) [] p ->
  data_at sh (tarray tuint k) a p * data_at sh tuint v (offset_val (4 * k) p) *
  data_at sh (tarray tuint r) b (offset_val (4 * (k + 1)) p) |--
  data_at sh (tarray tuint m) (a ++ [v] ++ b) p.
Proof. intros. subst. apply slot_join; auto. Qed.
End Slot.

(* The model side of one iteration. *)
Lemma loop1_utf8_len (c: Z): 0 <= Zlength (utf8 c) <= 4.
Proof.
  unfold utf8.
  destruct (c <? 128); [ | destruct (c <? 2048); [ | destruct (c <? 65536); [ | destruct (c <=? 1114111)]]];
    rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma loop1_utf8s_len (cps: list Z): 0 <= Zlength (utf8s cps) <= 4 * Zlength cps.
Proof.
  induction cps as [ | c r IH]; unfold utf8s in *; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons. pose proof (loop1_utf8_len c). lia.
Qed.

Lemma loop1_ulen_bounds (cps: list Z): 1 <= ulen_of cps <= 4 * Zlength cps + 1.
Proof. unfold ulen_of. pose proof (loop1_utf8s_len cps). lia. Qed.

Lemma loop1_ulen_snoc (pre: list Z) (c: Z): 0 <= c <= 1114111 ->
  ulen_of (pre ++ [c]) =
  ulen_of pre + (if c <? 128 then 1 else if c <? 2048 then 2 else if c <? 65536 then 3 else 4).
Proof.
  intros Hc. unfold ulen_of, utf8s. rewrite map_app, concat_app, Zlength_app. simpl. rewrite app_nil_r.
  unfold utf8.
  destruct (c <? 128); [ | destruct (c <? 2048); [ | destruct (c <? 65536); [ | destruct (c <=? 1114111) eqn:E]]];
    rewrite ?Zlength_cons, ?Zlength_nil; try lia.

Qed.

Lemma loop1_one_label_snoc (pre: list Z) (c: Z):
  one_label_ok (pre ++ [c]) = (one_label_ok pre && (negb (c =? 46) && negb (c =? 0)))%bool.
Proof. unfold one_label_ok. rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity. Qed.
