(* Piece 4 of the main of harness/x_decode.c: nondet_bytes(enc, len) when len != 0, copy_bytes, pick(cap) (DecMainDefs). *)
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

(* QuickProof's nondet_bytes takes buf = NULL when n = 0; here buf is a pointer (isptr, or a field_compatible
   fact), so the specification's conditional pre- and postcondition are their non-NULL branch. *)
Ltac nonnull_tac := let H := fresh in intro H;
  first [ assumption
        | match goal with Hp: ?p <> nullval |- _ => rewrite H in Hp; contradiction end
        | match goal with Hp: isptr ?p |- _ => rewrite H in Hp; simpl in Hp; contradiction end
        | match goal with Hp: field_compatible _ _ ?p |- _ =>
            rewrite H in Hp; destruct Hp as [Hp _]; simpl in Hp; contradiction end ].
Local Open Scope logic.

#[local] Instance CCE_rt : change_composite_env OpensslPunycode.proof.harness.RefRt.CS CS := CCE_any _ _.
#[local] Instance CCE_rt' : change_composite_env CS OpensslPunycode.proof.harness.RefRt.CS := CCE_any _ _.

Lemma tuint_as_bytes sh p: data_at_ sh tuint p |-- !! field_compatible tuint [] p && data_at_ sh (tarray tuchar 4) p.
Proof.
  assert_PROP (field_compatible tuint [] p) as FC by entailer!.
  sep_apply (data_at__memory_block_cancel sh tuint p).
  sep_apply (memory_block_data_at__tarray_tuchar sh p (sizeof tuint) ltac:(simpl; rep_lia)).
  entailer!.
Qed.

Lemma piece4 : piece7_stmt -> piece4_stmt.
Proof.
  intros H7 Espec gv vc vo vd n pe ps. unfold pre4, T4, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward_if (EX bs: list Z,
    PROP (bytes_ok bs; Zlength bs = n)
    LOCAL (temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr n));
           gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
    SEP (arr0 Ews tuchar n (vb bs) pe; arr0 Ews tuchar n (Zrepeat Vundef n) ps;
         data_at_ Tsh tuint vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
  { assert (Hn: n <> 0) by (intro; subst n; contradiction H0; reflexivity).
    unfold arr0 at 1. rewrite if_false by auto.
    change (Zrepeat Vundef n) with (Zrepeat (default_val tuchar) n) at 1.
    rewrite <- data_at__tarray.
    assert_PROP (field_compatible (tarray tuchar n) [] pe) as FCe by entailer!.
    forward_call (pe, n, Ews).
    { rewrite if_false by nonnull_tac. cancel. }
    Intros bs. rewrite if_false by nonnull_tac. Exists bs. entailer!. unfold arr0. rewrite !if_false by auto. cancel. }
  { forward. Exists (@nil Z).
    assert (Hn: n = 0).
    { apply (f_equal Int64.unsigned) in H0. rewrite Int64.unsigned_repr in H0 by rep_lia. exact H0. }
    subst n. unfold arr0. rewrite !if_true by auto. entailer!. constructor. }
  Intros bs. subst n.
  rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ pe).
  rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ ps).
  forward_call (Ews, ps, Zrepeat Vundef (Zlength bs), Ews, pe, bs).
  { apply Zlength_Zrepeat; lia. }
  rewrite <- (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ pe).
  rewrite <- (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ ps).
  sep_apply (tuint_as_bytes Tsh vc). Intros. rename H1 into FCc.
  forward_call (vc, 4, Tsh).
  { rewrite if_false by nonnull_tac. cancel. }
  Intros cb. rewrite if_false by nonnull_tac.
  sep_apply (pick_tuint Tsh cb vc H1 H2 FCc).
  Intros v.
  eapply semax_pre; [ | apply (H7 Espec gv vc vo vd bs pe ps (Int.unsigned v)) ].
  unfold pre7. rewrite Int.repr_unsigned. entailer!.
Qed.
