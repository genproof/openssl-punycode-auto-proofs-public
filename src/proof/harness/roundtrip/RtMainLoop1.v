(* A piece of the main of harness/x_roundtrip.c (see MainDefs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.

Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLoop1A.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLoop1B.

(* QuickProof's nondet_bytes takes buf = NULL when n = 0; here buf is a pointer (isptr, or a field_compatible
   fact), so the specification's conditional pre- and postcondition are their non-NULL branch. *)
Ltac nonnull_tac := let H := fresh in intro H;
  first [ assumption
        | match goal with Hp: ?p <> nullval |- _ => rewrite H in Hp; contradiction end
        | match goal with Hp: isptr ?p |- _ => rewrite H in Hp; simpl in Hp; contradiction end
        | match goal with Hp: field_compatible _ _ ?p |- _ =>
            rewrite H in Hp; destruct Hp as [Hp _]; simpl in Hp; contradiction end ].
Local Open Scope logic.

Lemma piece_loop1 : piece_ecap_stmt -> piece_loop1_stmt.
Proof.
  intros H. unfold piece_loop1_stmt. intros.
  unfold P_loop1, stmt_loop1, main_frame, main_ret, main_post. abbreviate_semax.
  Intros.
  forward_for_simple_bound m
    (EX j: Z, EX pre: list Z,
     PROP (Zlength pre = j; Forall (fun c => 0 <= c <= 1114111) pre)
     LOCAL (temp _ulen (Vlong (Int64.repr (ulen_of pre)));
            temp _one_label (Vint (Int.repr (if one_label_ok pre then 1 else 0))); temp _cps pc;
            temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
     SEP (arr0 Ews tuint m (vb pre ++ Zrepeat Vundef (m - j)) pc;
          data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
          OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT)).
  - Exists (@nil Z). simpl vb. rewrite app_nil_l, Z.sub_0_r. entailer!.
  - Intros.
    unfold arr0 at 1. rewrite if_false by lia.
    replace (m - i) with (1 + (m - i - 1)) by lia. rewrite <- Zrepeat_app by lia.
    change (Zrepeat Vundef 1) with [Vundef].
    assert (Lv: Zlength (vb pre) = i) by (unfold vb; rewrite Zlength_map; lia).
    sep_apply (slot_split_k Ews m i (m - i - 1) (vb pre) (Zrepeat Vundef (m - i - 1)) Vundef pc Lv
                 ltac:(rewrite Zlength_Zrepeat; lia) ltac:(lia)).
    Intros.
    forward_call (offset_val (4 * i) pc, 4, Ews).
    { rewrite if_false by nonnull_tac. cancel. }
    Intros bs. rewrite if_false by nonnull_tac.
    sep_apply (pick_tuint Ews bs _ H6 H7 H5).
    Intros v.
    set (c := Int.unsigned v). pose proof (Int.unsigned_range_2 v) as Hc.
    rewrite <- (Int.repr_unsigned v). fold c.
    sep_apply (slot_join_k Ews m i (m - i - 1) (vb pre) (Zrepeat Vundef (m - i - 1)) (Vint (Int.repr c)) pc Lv
                 ltac:(rewrite Zlength_Zrepeat; lia) ltac:(lia) ltac:(assumption)).
    replace (vb pre ++ [Vint (Int.repr c)] ++ Zrepeat Vundef (m - i - 1))
      with (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1)))
      by (rewrite vb_app, <- app_assoc; replace (m - (i + 1)) with (m - i - 1) by lia; reflexivity).
    assert (Hz: forall d: Inhabitant val, @Znth val d i (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))) = Vint (Int.repr c)).
    { intros d. rewrite app_Znth1 by (unfold vb; rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil; lia).
      unfold vb. rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      rewrite app_Znth2 by lia. rewrite H2, Z.sub_diag. reflexivity. }
    forward.
    { entailer!. rewrite Hz. exact I. }
    rewrite Hz.
    forward_call (Int.repr (if c <=? 1114111 then 1 else 0)).
    { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
      destruct (zlt 1114111 c), (c <=? 1114111) eqn:E; try reflexivity;
        [apply Z.leb_le in E | apply Z.leb_gt in E]; lia. }
    assert (Hc2: c <= 1114111)
      by (destruct (c <=? 1114111) eqn:E; [apply Z.leb_le in E; lia | contradiction H8; reflexivity]).
    clear H8. assert (Hc0: 0 <= c) by (unfold c; lia). clearbody c. clear Hc.
    apply (loop1_rest Espec gv m pc vo ve i pre c); auto.
  - Intros pre. rewrite Z.sub_diag, Zrepeat_0, app_nil_r. subst m.
    eapply semax_pre; [ | apply (H Espec gv pre pc vo ve) ].
    unfold P_ecap, main_frame. entailer!.
Qed.
