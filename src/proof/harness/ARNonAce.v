(* pr_a2ulabel: a label without the ACE prefix is written as it is: pr_put(k, s + st, m). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

(* A string array cut into [0, a), [a, b), [b, n): each part an arr0 (emp when empty). *)
Lemma arr0_zero_emp: forall sh m (v: list val) p, isptr p -> m = 0 -> Zlength v = m ->
  data_at sh (tarray tuchar m) v p = emp.
Proof.
  intros. subst. apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_eq; auto.
Qed.

Lemma arr0_split3: forall sh n a b (l: list Z) p, 0 <= a <= b -> b <= n -> Zlength l = n -> isptr p ->
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
  [rewrite (arr0_zero_emp sh a) by auto | ];
  (destruct (Z.eq_dec (b - a) 0) as [Hba|Hba];
   [rewrite (arr0_zero_emp sh (b - a)) by (auto; normalize) | ]);
  (destruct (Z.eq_dec (n - b) 0) as [Hnb|Hnb];
   [rewrite (arr0_zero_emp sh (n - b)) by (auto; normalize) | ]); auto.
Qed.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma nonace_piece: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  is_ace (lab s st) = false ->
  semax Delta_a2u (lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) s_nonace
    (overridePost (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k) R).
Proof.
  intros R Hctx Hit Hace. unfold lab_pre, lab_post. abbreviate_semax.
  destruct Hctx as (Hshs & Hshk & Hshb & Hshc & Hbs & Hls & Hcap & Hinit & Hps).
  destruct Hit as (Hst & Hk & Hcv & HA).
  pose proof (lab_end_range s st Hst) as He.
  assert (Hll: Zlength (lab s st) = lab_end s st - st) by (unfold lab; rewrite Zlength_sublist; lia).
  assert (Hbl: bytes_ok (lab s st)) by (unfold lab, bytes_ok in *; apply Forall_sublist; auto).
  assert_PROP (0 < Zlength s -> field_compatible (tarray tuchar (Zlength s)) [] ps) as Hfc.
  { unfold arr0. destruct (Z.eq_dec (Zlength s) 0); entailer!. }
  rewrite (arr0_split3 shs (Zlength s) st (lab_end s st) s ps) by (auto; lia).
  fold (lab s st). rewrite <- Hll.
  destruct R. unfold s_nonace. Intros.
  forward_call (shk, pk, buf, cap, k, init, shb, shs, offset_val st ps, lab s st).
  { destruct Hk. split; [auto | lia]. }
  Exists (put cap k (lab s st)) cv.
  rewrite (arr0_split3 shs (Zlength s) st (lab_end s st) s ps) by (auto; lia).
  fold (lab s st). rewrite <- Hll.
  entailer!.
  split.
  - unfold label_step. rewrite Hace. auto.
  - apply put_ok; auto.
Qed.

End Piece.
