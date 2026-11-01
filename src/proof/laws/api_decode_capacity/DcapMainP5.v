(* Piece 5 of the main of harness/api_decode_capacity.c: the NULL test of input, out and saved (DcapMainDefs).  Past
   it, the three blocks are arrays (nothing when empty) and their malloc tokens are dropped. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.
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

Lemma mblock_un_tc n q P: 0 <= n -> mblock_un n q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold mblock_un. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof (tarray tuint n))).
    + sep_apply (data_at__valid_ptr Ews (tarray tuint n) q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews (tarray tuint n) q); [ lia | ]. entailer!.
Qed.

(* A block of n elements is an array of n elements (nothing when n = 0). *)
Lemma data_at_arr0 {cs: compspecs} sh t n v q: data_at sh (tarray t n) v q |-- arr0 sh t n v q * TT.
Proof. unfold arr0. destruct (Z.eq_dec n 0). - rewrite emp_sepcon. apply TT_right. - cancel. Qed.

(* A non-NULL pointer or NULL is a pointer. *)
Lemma nonnull_isptr q: is_pointer_or_null q -> q <> nullval -> isptr q.
Proof. intros H N. destruct q; simpl in *; auto; try contradiction. subst. exfalso; apply N; reflexivity. Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece5 : piece6_stmt -> piece5_stmt.
Proof.
  intros H6 Espec gv vc ve vf bs pi c init po ps. unfold pre5, lvars3, T5, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq po nullval then 1 else 0)))).
  { apply derives_trans with (mblock_uc (Zlength bs) (vb bs) pi * TT); [ cancel | apply mblock_uc_tc; rep_lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with (mblock_ui c (vb init) po * TT); [ cancel | apply mblock_ui_tc; lia ]. }
    entailer!. destruct (Val.eq pi nullval); [ contradiction | ].
    destruct (Val.eq po nullval); [ subst; reflexivity | ].
    nonnull_cmp po. }
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq po nullval then 1 else
    if Val.eq ps nullval then 1 else 0)))).
  { forward. entailer!. destruct (Val.eq pi nullval); [ reflexivity | ].
    destruct (Val.eq po nullval); [ reflexivity | ]. exfalso; apply H4'; reflexivity. }
  { forward.
    { go_lower. apply derives_trans with (mblock_un c ps * TT); [ cancel | apply mblock_un_tc; lia ]. }
    entailer!. destruct (Val.eq pi nullval); [ discriminate | ]. destruct (Val.eq po nullval); [ discriminate | ].
    destruct (Val.eq ps nullval); [ subst; reflexivity | ]. nonnull_cmp ps. }
  forward_if (pre6 gv vc ve vf bs pi c init po ps).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward.
    destruct (Val.eq pi nullval); [ discriminate | ]. destruct (Val.eq po nullval); [ discriminate | ].
    destruct (Val.eq ps nullval); [ discriminate | ].
    unfold pre6, lvars3, mblock_uc, mblock_ui, mblock_un. rewrite !if_false by auto.
    sep_apply (data_at_arr0 Ews tuchar (Zlength bs) (vb bs) pi).
    sep_apply (data_at_arr0 Ews tuint c (vb init) po).
    unfold data_at_, field_at_.
    change (field_at Ews (tarray tuint c) [] (default_val (tarray tuint c)) ps) with
      (data_at Ews (tarray tuint c) (Zrepeat Vundef c) ps).
    sep_apply (data_at_arr0 Ews tuint c (Zrepeat Vundef c) ps).
    entailer!. split; apply nonnull_isptr; auto. }
  apply H6.
Qed.
