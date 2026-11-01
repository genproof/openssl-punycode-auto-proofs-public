(* Piece 7 of the main of harness/api_decode_deterministic.c: the NULL test of first, second, out1 and out2
   (DdetMainDefs).  Past it, the first len octets of first are the input, the other octets are dropped. *)
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

(* The first m octets of a block of n octets are an array of their own. *)
Lemma data_at_prefix_uc {cs: compspecs} sh n m bs q:
  0 <= m <= n -> Zlength bs = n ->
  data_at sh (tarray tuchar n) (vb bs) q |-- arr0 sh tuchar m (vb (sublist 0 m bs)) q * TT.
Proof.
  intros Hm Hb. unfold arr0. destruct (Z.eq_dec m 0).
  - rewrite emp_sepcon. apply TT_right.
  - change (tarray tuchar n) with (Tarray tuchar n noattr).
    rewrite (split2_data_at_Tarray_tuchar sh n m (vb bs) q) by (rewrite ?Zlength_vb; lia).
    unfold vb. rewrite sublist_map. cancel.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece7 : piece8_stmt -> piece7_stmt.
Proof.
  intros H8 Espec gv v1 v2 bs len pf ps c vs1 vs2 po1 po2. unfold pre7, T7, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pf nullval then 1 else if Val.eq ps nullval then 1 else 0)))).
  { apply derives_trans with (mblock_uc (Zlength bs) (vb bs) pf * TT); [ cancel | apply mblock_uc_tc; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with (mblock_uc len (vb (sublist 0 len bs)) ps * TT);
        [ cancel | apply mblock_uc_tc; lia ]. }
    entailer!. destruct (Val.eq pf nullval); [ contradiction | ].
    destruct (Val.eq ps nullval); [ subst; reflexivity | ].
    nonnull_cmp ps. }
  forward_if (temp _t'9 (Vint (Int.repr (if Val.eq pf nullval then 1 else if Val.eq ps nullval then 1 else
    if Val.eq po1 nullval then 1 else 0)))).
  { forward. entailer!. destruct (Val.eq pf nullval); [ reflexivity | ].
    destruct (Val.eq ps nullval); [ reflexivity | ]. exfalso; apply H9'; reflexivity. }
  { forward.
    { go_lower. apply derives_trans with (mblock_ui c (vb vs1) po1 * TT); [ cancel | apply mblock_ui_tc; lia ]. }
    entailer!. destruct (Val.eq pf nullval); [ discriminate | ]. destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ subst; reflexivity | ]. nonnull_cmp po1. }
  forward_if (temp _t'10 (Vint (Int.repr (if Val.eq pf nullval then 1 else if Val.eq ps nullval then 1 else
    if Val.eq po1 nullval then 1 else if Val.eq po2 nullval then 1 else 0)))).
  { forward. entailer!. destruct (Val.eq pf nullval); [ reflexivity | ].
    destruct (Val.eq ps nullval); [ reflexivity | ]. destruct (Val.eq po1 nullval); [ reflexivity | ].
    exfalso; apply H9'; reflexivity. }
  { forward.
    { go_lower. apply derives_trans with (mblock_ui c (vb vs2) po2 * TT); [ cancel | apply mblock_ui_tc; lia ]. }
    entailer!. destruct (Val.eq pf nullval); [ discriminate | ]. destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ subst; reflexivity | ]. nonnull_cmp po2. }
  forward_if (pre8 gv v1 v2 (sublist 0 len bs) pf ps c vs1 vs2 po1 po2).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward.
    destruct (Val.eq pf nullval); [ discriminate | ]. destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ]. destruct (Val.eq po2 nullval); [ discriminate | ].
    unfold pre8, mblock_uc, mblock_ui. rewrite !if_false by auto.
    sep_apply (data_at_prefix_uc Ews (Zlength bs) len bs pf ltac:(lia) eq_refl).
    sep_apply (data_at_arr0_uc Ews len (vb (sublist 0 len bs)) ps).
    sep_apply (data_at_arr0_ui Ews c (vb vs1) po1).
    sep_apply (data_at_arr0_ui Ews c (vb vs2) po2).
    rewrite Zlength_sublist by lia. replace (len - 0) with len by lia.
    entailer!. apply Forall_sublist; auto. }
  apply H8.
Qed.
