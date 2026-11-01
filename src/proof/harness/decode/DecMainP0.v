(* Piece 0 of the main of harness/x_decode.c: len, the mallocs of enc and snap, their NULL test (DecMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.proof.harness.decode.DecMainDefs.

Lemma malloc_tc_test0 (t: type) (p: val) (P: mpred):
  0 <= sizeof t ->
  (if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p) * P
  |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof t)).
    + sep_apply (data_at__valid_ptr Ews t p); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews t p); [ lia | ]. entailer!.
Qed.

Lemma malloc_arr0_tuchar (m: Z) (pc: val):
  0 <= m -> (pc <> nullval \/ m = 0) ->
  (if eq_dec pc nullval then emp else malloc_token Ews (tarray tuchar m) pc * data_at_ Ews (tarray tuchar m) pc)
  |-- arr0 Ews tuchar m (Zrepeat Vundef m) pc * TT.
Proof.
  intros Hm Hpc. unfold arr0. destruct (eq_dec pc nullval).
  - destruct Hpc as [Hpc | ->]; [ contradiction | ]. rewrite if_true by auto. entailer!.
  - destruct (Z.eq_dec m 0); [ entailer! | ]. unfold data_at_, field_at_. entailer!.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece0 : piece4_stmt -> piece0_stmt.
Proof.
  intros H4 Espec gv vc vo vd. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call. Intros n.
  forward_call (tarray tuchar n, gv).
  { simpl; rep_lia. }
  Intros pe.
  forward_call (tarray tuchar n, gv).
  { simpl; rep_lia. }
  Intros ps.
  forward_if (temp _t'4 (Vint (Int.repr (if Val.eq pe nullval then 1 else if Val.eq ps nullval then 1 else 0)))).
  { apply derives_trans with ((if eq_dec pe nullval then emp else malloc_token Ews (tarray tuchar n) pe *
      data_at_ Ews (tarray tuchar n) pe) * TT)%logic; [ cancel | apply malloc_tc_test0; simpl; rep_lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with ((if eq_dec ps nullval then emp else malloc_token Ews (tarray tuchar n) ps *
        data_at_ Ews (tarray tuchar n) ps) * TT)%logic; [ cancel | apply malloc_tc_test0; simpl; rep_lia ]. }
    entailer!. destruct (Val.eq pe nullval); [ contradiction | ].
    destruct (Val.eq ps nullval); [ subst; reflexivity | ].
    nonnull_cmp ps. }
  forward_if (temp _t'5 (Vint (Int.repr (if Z.eq_dec n 0 then 0 else
    if Val.eq pe nullval then 1 else if Val.eq ps nullval then 1 else 0)))).
  { forward. entailer!.
    assert (E: (if Val.eq pe nullval then 1 else if Val.eq ps nullval then 1 else 0) = 1)
      by (destruct (Val.eq pe nullval); [ | destruct (Val.eq ps nullval)]; lia).
    rewrite E. destruct (Z.eq_dec n 0) as [-> | Hn]; [ reflexivity | ].
    unfold Int64.cmpu. rewrite Int64.eq_false; [ reflexivity | ].
    intro X; apply (f_equal Int64.unsigned) in X; rewrite !Int64.unsigned_repr in X by rep_lia; lia. }
  { forward. entailer!.
    destruct (Z.eq_dec n 0); [ reflexivity | ].
    destruct (Val.eq pe nullval); [ discriminate | ]. destruct (Val.eq ps nullval); [ discriminate | reflexivity ]. }
  forward_if (pre4 gv vc vo vd n pe ps).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. unfold pre4.
    assert (Hpe: pe <> nullval \/ n = 0).
    { destruct (Z.eq_dec n 0); [ right; auto | left ].
      destruct (Val.eq pe nullval); [ discriminate | auto ]. }
    assert (Hps: ps <> nullval \/ n = 0).
    { destruct (Z.eq_dec n 0); [ right; auto | left ].
      destruct (Val.eq pe nullval); [ discriminate | ].
      destruct (Val.eq ps nullval); [ discriminate | auto ]. }
    sep_apply (malloc_arr0_tuchar n pe); [ lia | auto ].
    sep_apply (malloc_arr0_tuchar n ps); [ lia | auto ].
    entailer!. }
  apply H4.
Qed.
