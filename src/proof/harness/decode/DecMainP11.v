(* Piece 11 of the main of harness/x_decode.c: the loop that picks out[j] and copies it to want[j] (DecMainDefs). *)
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
Require OpensslPunycode.proof.harness.roundtrip.RtMainLoop1A.

(* QuickProof's nondet_bytes takes buf = NULL when n = 0; here buf is a pointer (isptr, or a field_compatible
   fact), so the specification's conditional pre- and postcondition are their non-NULL branch. *)
Ltac nonnull_tac := let H := fresh in intro H;
  first [ assumption
        | match goal with Hp: ?p <> nullval |- _ => rewrite H in Hp; contradiction end
        | match goal with Hp: isptr ?p |- _ => rewrite H in Hp; simpl in Hp; contradiction end
        | match goal with Hp: field_compatible _ _ ?p |- _ =>
            rewrite H in Hp; destruct Hp as [Hp _]; simpl in Hp; contradiction end ].
Local Open Scope logic.

Module L1 := OpensslPunycode.proof.harness.roundtrip.RtMainLoop1A.

Definition inv11 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (c: Z) (po pw: val) (jt j: Z) (pre: list Z)
    : environ -> mpred :=
  PROP (0 <= j <= c; Zlength pre = j; Forall (fun x => 0 <= x <= Int.max_unsigned) pre)
  LOCAL (temp _j (Vlong (Int64.repr jt));
         temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuint c (vb pre ++ Zrepeat Vundef (c - j)) po; arr0 Ews tuint c (vb pre ++ Zrepeat Vundef (c - j)) pw;
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr c)) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

Lemma piece11 : piece12_stmt -> piece11_stmt.
Proof.
  intros H12 Espec gv vc vo vd bs pe ps c po pw. unfold pre11, T11, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward.
  forward_loop (EX j: Z, EX pre: list Z, inv11 gv vc vo vd bs pe ps c po pw j j pre)
    continue: (EX j: Z, EX pre: list Z, inv11 gv vc vo vd bs pe ps c po pw j (j + 1) pre)
    break: (EX pre: list Z, inv11 gv vc vo vd bs pe ps c po pw c c pre).
  - Exists 0 (@nil Z). unfold inv11. simpl vb. rewrite app_nil_l, Z.sub_0_r. entailer!.
  - Intros j pre. unfold inv11. Intros.
    forward.
    forward_if.
    + rewrite Int.unsigned_repr in H5 by rep_lia.
      assert (Hc: c <> 0) by lia.
      unfold arr0 at 1 2. rewrite !if_false by auto.
      replace (c - j) with (1 + (c - j - 1)) by lia. rewrite <- Zrepeat_app by lia.
      change (Zrepeat Vundef 1) with [Vundef].
      assert (Lv: Zlength (vb pre) = j) by (unfold vb; rewrite Zlength_map; lia).
      sep_apply (L1.slot_split_k Ews c j (c - j - 1) (vb pre) (Zrepeat Vundef (c - j - 1)) Vundef po Lv
                   ltac:(rewrite Zlength_Zrepeat; lia) ltac:(lia)).
      Intros.
      forward_call (offset_val (4 * j) po, 4, Ews).
      { rewrite if_false by nonnull_tac. cancel. }
      Intros cb. rewrite if_false by nonnull_tac.
      sep_apply (pick_tuint Ews cb _ H8 H9 H7).
      Intros v.
      set (x := Int.unsigned v). assert (Hx: 0 <= x <= Int.max_unsigned) by (unfold x; apply Int.unsigned_range_2).
      rewrite <- (Int.repr_unsigned v). fold x.
      sep_apply (L1.slot_join_k Ews c j (c - j - 1) (vb pre) (Zrepeat Vundef (c - j - 1)) (Vint (Int.repr x)) po Lv
                   ltac:(rewrite Zlength_Zrepeat; lia) ltac:(lia) H6).
      replace (vb pre ++ [Vint (Int.repr x)] ++ Zrepeat Vundef (c - j - 1))
        with (vb (pre ++ [x]) ++ Zrepeat Vundef (c - (j + 1)))
        by (rewrite vb_app, <- app_assoc; replace (c - (j + 1)) with (c - j - 1) by lia; reflexivity).
      assert (Hz: forall d: Inhabitant val,
                @Znth val d j (vb (pre ++ [x]) ++ Zrepeat Vundef (c - (j + 1))) = Vint (Int.repr x)).
      { intros d. rewrite app_Znth1 by (unfold vb; rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil; lia).
        unfold vb. rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        rewrite app_Znth2 by lia. rewrite H3, Z.sub_diag. reflexivity. }
      forward.
      { entailer!. rewrite Hz. exact I. }
      rewrite Hz.
      forward.
      clearbody x.
      assert (Hw: upd_Znth j (vb pre ++ [Vundef] ++ Zrepeat Vundef (c - j - 1)) (Vint (Int.repr x)) =
                  vb (pre ++ [x]) ++ Zrepeat Vundef (c - (j + 1))).
      { rewrite vb_app. replace (c - (j + 1)) with (c - j - 1) by lia.
        rewrite upd_Znth_app2 by (rewrite Lv; list_solve). rewrite Lv, Z.sub_diag. rewrite <- app_assoc. f_equal.
        rewrite upd_Znth_app1 by (rewrite Zlength_cons, Zlength_nil; lia). reflexivity. }
      rewrite Hw.
      Exists j (pre ++ [x]). unfold inv11. entailer!.
      * split; [ list_solve | apply Forall_app; split; auto ].
      * unfold arr0. rewrite !if_false by auto. cancel.
    + rewrite Int.unsigned_repr in H5 by rep_lia.
      assert (j = c) by lia. subst j.
      forward. Exists pre. unfold inv11. entailer!.
  - Intros j pre. unfold inv11. Intros.
    forward.
    Exists (j + 1) pre. unfold inv11. entailer!.
  - Intros pre. unfold inv11. Intros.
    rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
    subst c.
    eapply semax_pre; [ | apply (H12 Espec gv vc vo vd bs pe ps pre po pw) ].
    unfold pre12. entailer!.
Qed.
