(* Piece 8 of the main of harness/api_decode_deterministic.c: the two calls of ossl_punycode_decode and the checks
   (DdetMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetMainDefs.
Require OpensslPunycode.proof.harness.ARDecRange.
Require OpensslPunycode.proof.punycode.DecModel.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

(* ossl_punycode_decode's specification moves to the law's compspecs (its arrays are scalars). *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.

(* The result and the reported length of ossl_punycode_decode do not depend on the array's initial values. *)
Lemma dres_r inp c i1 i2:
  fst (fst (PS.decode_result inp c i1)) = fst (fst (PS.decode_result inp c i2)).
Proof. unfold PS.decode_result. destruct (Int.max_unsigned <=? Zlength inp); [ reflexivity | ].
  destruct (decode inp c) as [ok out]; reflexivity. Qed.

Lemma dres_n inp c i1 i2: snd (PS.decode_result inp c i1) = snd (PS.decode_result inp c i2).
Proof. unfold PS.decode_result. destruct (Int.max_unsigned <=? Zlength inp); [ reflexivity | ].
  destruct (decode inp c) as [ok out]; reflexivity. Qed.

(* The first elements of an array of c unsigned ints are an array of their own. *)
Lemma arr0_prefix_ui {cs: compspecs} sh c (l1 l2: list val) q:
  Zlength l1 <= c -> Zlength l2 = c - Zlength l1 ->
  arr0 sh tuint c (l1 ++ l2) q |-- arr0 sh tuint (Zlength l1) l1 q * TT.
Proof.
  intros H1 H2. pose proof (Zlength_nonneg l1). unfold arr0.
  destruct (Z.eq_dec (Zlength l1) 0) as [E | E].
  - rewrite emp_sepcon. apply TT_right.
  - rewrite if_false by lia.
    rewrite (split2_data_at_Tarray_app (Zlength l1) c sh tuint l1 l2) by auto. cancel.
Qed.

Lemma piece8 : piece8_stmt.
Proof.
  intros Espec gv v1 v2 inp pf ps c vs1 vs2 po1 po2. unfold pre8, T8, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward. forward.
  forward_call (gv, Ews, pf, inp, Ews, po1, c, vb vs1, Tsh, v1).
  { rewrite Zlength_vb; auto. }
  forward_call (gv, Ews, ps, inp, Ews, po2, c, vb vs2, Tsh, v2).
  { rewrite Zlength_vb; auto. }
  rewrite (dres_r inp c (vb vs2) (vb vs1)), (dres_n inp c (vb vs2) (vb vs1)).
  forward_if (temp _t'13 (Vint Int.one)).
  { forward. forward. forward. entailer!. simpl. rewrite Int.eq_true. reflexivity. }
  { contradiction. }
  forward_call (Int.one).
  forward_if (PROP () LOCAL (lvar _count1 tuint v1; lvar _count2 tuint v2)
              SEP (data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; TT)).
  { assert (Hlt: Zlength inp < Int.max_unsigned).
    { unfold PS.decode_result in H4. destruct (Int.max_unsigned <=? Zlength inp) eqn:EB.
      - simpl in H4. apply (f_equal Int.unsigned) in H4. rewrite !Int.unsigned_repr in H4 by rep_lia. lia.
      - apply Z.leb_gt in EB. lia. }
    destruct (decode inp c) as [ok out] eqn:HD.
    pose proof (OpensslPunycode.proof.punycode.DecModel.decode_result_eq inp c (vb vs1) ok out Hlt HD) as E1.
    pose proof (OpensslPunycode.proof.punycode.DecModel.decode_result_eq inp c (vb vs2) ok out Hlt HD) as E2.
    rewrite E1, E2 in *.
    destruct ok; simpl fst in *; simpl snd in *.
    2: { apply (f_equal Int.unsigned) in H4. rewrite !Int.unsigned_repr in H4 by rep_lia. lia. }
    pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range inp c H (proj1 H1)) as [Hr Hl].
    rewrite HD in Hr, Hl. simpl in Hr, Hl. pose proof (Zlength_nonneg out).
    forward.
    sep_apply (arr0_prefix_ui Ews c (vb out) (sublist (Zlength out) c (vb vs1)) po1).
    { rewrite Zlength_vb; lia. }
    { rewrite Zlength_sublist by (rewrite ?Zlength_vb; lia). rewrite !Zlength_vb; lia. }
    sep_apply (arr0_prefix_ui Ews c (vb out) (sublist (Zlength out) c (vb vs2)) po2).
    { rewrite Zlength_vb; lia. }
    { rewrite Zlength_sublist by (rewrite ?Zlength_vb; lia). rewrite !Zlength_vb; lia. }
    rewrite Zlength_vb. Intros.
    rewrite (arr0_tuint_cs CS CM.CS Ews (Zlength out) _ po1).
    rewrite (arr0_tuint_cs CS CM.CS Ews (Zlength out) _ po2).
    forward_call (Ews, po1, out, Ews, po2, out).
    destruct (list_eq_dec Z.eq_dec out out) as [_ | NE]; [ | contradiction NE; reflexivity ].
    forward_call (Int.repr 1).
    entailer!. }
  { forward. entailer!. }
  forward. Exists (Int.repr 0). entailer!.
Qed.
