(* Piece 7 of the main of harness/rfc_unique.c: the NULL test of input1, input2, out1 and out2 (RunMainDefs).  Past
   it, each block is an array (nothing when empty), its token dropped. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunMainDefs.
Local Open Scope logic.

(* A pointer from malloc may be compared with NULL. *)
Lemma mblock_uc_tc n v q P: 0 <= n -> mblock_uc n v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold mblock_uc. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - sep_apply (data_at_data_at_ Ews (tarray tuchar n) v q).
    destruct (zlt 0 (sizeof (tarray tuchar n))).
    + sep_apply (data_at__valid_ptr Ews (tarray tuchar n) q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews (tarray tuchar n) q); [ lia | ]. entailer!.
Qed.

Lemma mblock_ui_tc n v q P: 0 <= n -> mblock_ui n v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold mblock_ui. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - sep_apply (data_at_data_at_ Ews (tarray tuint n) v q).
    destruct (zlt 0 (sizeof (tarray tuint n))).
    + sep_apply (data_at__valid_ptr Ews (tarray tuint n) q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews (tarray tuint n) q); [ lia | ]. entailer!.
Qed.

(* A block of n elements is an array of n elements (nothing when n = 0). *)
Lemma data_at_arr0_uc {cs: compspecs} sh n v q: data_at sh (tarray tuchar n) v q |-- arr0 sh tuchar n v q * TT.
Proof. unfold arr0. destruct (Z.eq_dec n 0). - rewrite emp_sepcon. apply TT_right. - cancel. Qed.

Lemma data_at_arr0_ui {cs: compspecs} sh n v q: data_at sh (tarray tuint n) v q |-- arr0 sh tuint n v q * TT.
Proof. unfold arr0. destruct (Z.eq_dec n 0). - rewrite emp_sepcon. apply TT_right. - cancel. Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece7 : piece8_stmt -> piece7_stmt.
Proof.
  intros H8 Espec gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2. unfold pre7, T7, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  pose proof (Zlength_nonneg bs1). pose proof (Zlength_nonneg bs2).
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pi1 nullval then 1 else if Val.eq pi2 nullval then 1 else 0)))).
  { apply derives_trans with (mblock_uc (Zlength bs1) (vb bs1) pi1 * TT); [ cancel | apply mblock_uc_tc; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with (mblock_uc (Zlength bs2) (vb bs2) pi2 * TT);
        [ cancel | apply mblock_uc_tc; lia ]. }
    entailer!. destruct (Val.eq pi1 nullval); [ contradiction | ].
    destruct (Val.eq pi2 nullval); [ subst; reflexivity | ].
    nonnull_cmp pi2. }
  forward_if (temp _t'9 (Vint (Int.repr (if Val.eq pi1 nullval then 1 else if Val.eq pi2 nullval then 1 else
    if Val.eq po1 nullval then 1 else 0)))).
  { forward. entailer!. destruct (Val.eq pi1 nullval); [ reflexivity | ].
    destruct (Val.eq pi2 nullval); [ reflexivity | ]. exfalso; lia. }
  { forward.
    { go_lower. apply derives_trans with (mblock_ui c (vb vs1) po1 * TT); [ cancel | apply mblock_ui_tc; lia ]. }
    entailer!. destruct (Val.eq pi1 nullval); [ discriminate | ]. destruct (Val.eq pi2 nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ subst; reflexivity | ]. nonnull_cmp po1. }
  forward_if (temp _t'10 (Vint (Int.repr (if Val.eq pi1 nullval then 1 else if Val.eq pi2 nullval then 1 else
    if Val.eq po1 nullval then 1 else if Val.eq po2 nullval then 1 else 0)))).
  { forward. entailer!. destruct (Val.eq pi1 nullval); [ reflexivity | ].
    destruct (Val.eq pi2 nullval); [ reflexivity | ]. destruct (Val.eq po1 nullval); [ reflexivity | ].
    exfalso; lia. }
  { forward.
    { go_lower. apply derives_trans with (mblock_ui c (vb vs2) po2 * TT); [ cancel | apply mblock_ui_tc; lia ]. }
    entailer!. destruct (Val.eq pi1 nullval); [ discriminate | ]. destruct (Val.eq pi2 nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ subst; reflexivity | ]. nonnull_cmp po2. }
  forward_if (pre8 gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward.
    destruct (Val.eq pi1 nullval); [ discriminate | ]. destruct (Val.eq pi2 nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ]. destruct (Val.eq po2 nullval); [ discriminate | ].
    unfold pre8, mblock_uc, mblock_ui. rewrite !if_false by auto.
    sep_apply (data_at_arr0_uc Ews (Zlength bs1) (vb bs1) pi1).
    sep_apply (data_at_arr0_uc Ews (Zlength bs2) (vb bs2) pi2).
    sep_apply (data_at_arr0_ui Ews c (vb vs1) po1).
    sep_apply (data_at_arr0_ui Ews c (vb vs2) po2).
    entailer!. }
  apply H8.
Qed.
