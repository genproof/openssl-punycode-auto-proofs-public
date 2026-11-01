(* Piece 7, second half, of the main of harness/x_decode.c: bytes, the mallocs of out and want, their NULL test (DecMainDefs). *)
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
Local Open Scope logic.


Lemma malloc_tc_test7 (t: type) (p: val) (P: mpred):
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

Lemma malloc_arr0_tuint7 (m: Z) (pc: val):
  0 <= m -> (pc <> nullval \/ m = 0) ->
  (if eq_dec pc nullval then emp else malloc_token Ews (tarray tuint m) pc * data_at_ Ews (tarray tuint m) pc)
  |-- arr0 Ews tuint m (Zrepeat Vundef m) pc * TT.
Proof.
  intros Hm Hpc. unfold arr0. destruct (eq_dec pc nullval).
  - destruct Hpc as [Hpc | ->]; [ contradiction | ]. rewrite if_true by auto. entailer!.
  - destruct (Z.eq_dec m 0); [ entailer! | ]. unfold data_at_, field_at_. entailer!.
Qed.

Ltac nonnull_cmp7 p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.


Definition T10 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 10 main_big.

(* After out = malloc(bytes); want = malloc(bytes): what malloc_spec' returned. *)
Definition pre10 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (c: Z) (po pw: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned)
  LOCAL (temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP ((if eq_dec po nullval then emp else malloc_token Ews (tarray tuint c) po * data_at_ Ews (tarray tuint c) po);
       (if eq_dec pw nullval then emp else malloc_token Ews (tarray tuint c) pw * data_at_ Ews (tarray tuint c) pw);
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr c)) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

Lemma piece7_test : piece11_stmt -> forall (Espec: OracleKind) gv vc vo vd bs pe ps c po pw,
  semax Delta_main (pre10 gv vc vo vd bs pe ps c po pw) (Ssequence T10 ret0) main_post.
Proof.
  intros H11 Espec gv vc vo vd bs pe ps c po pw. unfold pre10, T10, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq po nullval then 1 else if Val.eq pw nullval then 1 else 0)))).
  { apply derives_trans with ((if eq_dec po nullval then emp else malloc_token Ews (tarray tuint c) po *
      data_at_ Ews (tarray tuint c) po) * TT)%logic; [ cancel | apply malloc_tc_test7; simpl; rep_lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with ((if eq_dec pw nullval then emp else malloc_token Ews (tarray tuint c) pw *
        data_at_ Ews (tarray tuint c) pw) * TT)%logic; [ cancel | apply malloc_tc_test7; simpl; rep_lia ]. }
    entailer!. destruct (Val.eq po nullval); [ contradiction | ].
    destruct (Val.eq pw nullval); [ subst; reflexivity | ].
    nonnull_cmp7 pw. }
  forward_if (temp _t'9 (Vint (Int.repr (if Z.eq_dec c 0 then 0 else
    if Val.eq po nullval then 1 else if Val.eq pw nullval then 1 else 0)))).
  { forward. forward. entailer!.
    assert (E: (if Val.eq po nullval then 1 else if Val.eq pw nullval then 1 else 0) = 1)
      by (destruct (Val.eq po nullval); [ | destruct (Val.eq pw nullval)]; lia).
    rewrite E. destruct (Z.eq_dec c 0) as [-> | Hn]; [ reflexivity | ].
    destruct (zeq c 0); [ lia | reflexivity ]. }
  { forward. entailer!.
    destruct (Z.eq_dec c 0); [ reflexivity | ].
    destruct (Val.eq po nullval); [ discriminate | ]. destruct (Val.eq pw nullval); [ discriminate | reflexivity ]. }
  forward_if (pre11 gv vc vo vd bs pe ps c po pw).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. unfold pre11.
    assert (Hpo: po <> nullval \/ c = 0).
    { destruct (Z.eq_dec c 0); [ right; auto | left ].
      destruct (Val.eq po nullval); [ discriminate | auto ]. }
    assert (Hpw: pw <> nullval \/ c = 0).
    { destruct (Z.eq_dec c 0); [ right; auto | left ].
      destruct (Val.eq po nullval); [ discriminate | ].
      destruct (Val.eq pw nullval); [ discriminate | auto ]. }
    sep_apply (malloc_arr0_tuint7 c po); [ lia | auto ].
    sep_apply (malloc_arr0_tuint7 c pw); [ lia | auto ].
    entailer!. }
  apply H11.
Qed.
