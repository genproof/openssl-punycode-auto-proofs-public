(* Piece 21 of the main of harness/api_a2ulabel_labels.c: the three calls of ossl_a2ulabel (on s1, s2 and name)
   and the test of ossl_shim_zalloc_failed: past it, no allocation failed in any call (AlbMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module SS := OpensslPunycode.proof.shim.ShimSpec.

Lemma alb21_tint_cs (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma alb21_Zlength_str_of l: Zlength (str_of l) = first0 l.
Proof. pose proof (first0_range l). unfold str_of. rewrite Zlength_sublist by lia. lia. Qed.

(* A buffer a ++ [0] is l's string with its NUL, then the rest of the buffer. *)
Lemma alb21_split_s len a ps:
  Zlength a = len ->
  data_at Ews (tarray tuchar (len + 1)) (vb (a ++ [0])) ps =
  (SS.cstr Ews (str_of a) ps *
   data_at Ews (tarray tuchar (len - first0 a)) (vb (sublist (first0 a + 1) (len + 1) (a ++ [0])))
     (field_address0 (tarray tuchar (len + 1)) (SUB (first0 a + 1)) ps))%logic.
Proof.
  intros Hlen. pose proof (first0_range a) as Hr.
  unfold SS.cstr. rewrite (data_at_tuchar_cs SS.CS CS). rewrite alb21_Zlength_str_of.
  assert (E: a ++ [0] = (str_of a ++ [0]) ++ sublist (first0 a + 1) (len + 1) (a ++ [0])).
  { pose proof (first0_at a) as H0. unfold str_of.
    rewrite <- (sublist_same 0 (len + 1) (a ++ [0])) at 1 by list_solve.
    rewrite (sublist_split 0 (first0 a + 1) (len + 1)) by list_solve.
    f_equal. rewrite (sublist_split 0 (first0 a) (first0 a + 1)) by list_solve.
    rewrite sublist_app1 by lia. f_equal. rewrite sublist_len_1 by list_solve. rewrite H0. reflexivity. }
  rewrite E at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (first0 a + 1)).
  - replace (len + 1 - (first0 a + 1)) with (len - first0 a) by lia. reflexivity.
  - list_solve.
  - list_solve.
Qed.

(* The name's buffer: the string t1 '.' t2 with its NUL, then the uninitialized octets. *)
Lemma alb21_split_name n t rest pn:
  Zlength t + 1 + Zlength rest = n ->
  data_at Ews (tarray tuchar n) (vb (t ++ [0]) ++ rest) pn =
  (SS.cstr Ews t pn *
   data_at Ews (tarray tuchar (Zlength rest)) rest (field_address0 (tarray tuchar n) (SUB (Zlength t + 1)) pn))%logic.
Proof.
  intros Hn. unfold SS.cstr. rewrite (data_at_tuchar_cs SS.CS CS).
  rewrite (split2_data_at_Tarray_app (Zlength t + 1)).
  - replace (n - (Zlength t + 1)) with (Zlength rest) by lia. reflexivity.
  - rewrite Zlength_vb, Zlength_app. list_solve.
  - list_solve.
Qed.

(* A non-NULL output buffer of cap >= 1 octets, as ossl_a2ulabel_spec takes it (no malloc(0) token). *)
Lemma alb21_out_buf po cap v:
  po <> nullval -> cap <> 0 ->
  PS.out_buf Ews po cap v tk0 = data_at Ews (tarray tuchar cap) v po.
Proof.
  intros Hp Hc. unfold PS.out_buf, SS.zero_tok. rewrite if_false by auto. rewrite if_false by auto.
  rewrite sepcon_emp. apply data_at_tuchar_cs.
Qed.

(* The outcome of a call with a non-NULL buffer of cap >= 1 octets and no knob set: the model's, unless the
   allocation of the WPACKET record fails (mf), which gives -1, raises the failure flag and leaves the buffer. *)
Lemma alb21_outcome po cap s init zf mf:
  po <> nullval -> cap <> 0 ->
  PS.a2u_outcome po cap s init 0 zf mf =
  (if mf then -1 else fst (a2ulabel s cap), 0, if mf then 1 else zf,
   if mf then init else vb (snd (a2ulabel s cap)) ++ sublist (Zlength (snd (a2ulabel s cap))) cap init).
Proof.
  intros Hp Hc. unfold PS.a2u_outcome. rewrite if_false by auto.
  replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; auto). simpl.
  destruct mf; [ reflexivity | ]. destruct (a2ulabel s cap); reflexivity.
Qed.

Lemma piece21 : piece25_stmt -> piece21_stmt.
Proof.
  intros H25 Espec gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po.
  unfold pre21, T21, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  assert_PROP (isptr po1 /\ isptr po2 /\ isptr po) as Hp by entailer!.
  destruct Hp as (Hp1 & Hp2 & Hp).
  assert (Np1: po1 <> nullval) by (intro; subst; contradiction).
  assert (Np2: po2 <> nullval) by (intro; subst; contradiction).
  assert (Np: po <> nullval) by (intro; subst; contradiction).
  pose proof (first0_range a1). pose proof (first0_range a2).
  pose proof (str_of_ok a1 H2) as Hs1. pose proof (str_of_ok a2 H4) as Hs2.
  rewrite (alb21_split_s len1 a1 ps1) by auto.
  rewrite (alb21_split_s len2 a2 ps2) by auto.
  replace (vb (str_of a1 ++ [46] ++ str_of a2 ++ [0])) with (vb ((str_of a1 ++ [46] ++ str_of a2) ++ [0]))
    by (rewrite <- !app_assoc; reflexivity).
  rewrite (alb21_split_name (len1 + len2 + 2)) by
    (rewrite Zlength_Zrepeat, !Zlength_app, !alb21_Zlength_str_of by lia; list_solve).
  Intros.
  rewrite <- (alb21_out_buf po1 outlen1 (vb ob1)) by (auto; lia).
  rewrite <- (alb21_out_buf po2 outlen2 (vb ob2)) by (auto; lia).
  rewrite <- (alb21_out_buf po (outlen1 + outlen2) (vb ob)) by (auto; lia).
  forward_call (gv, Ews, ps1, str_of a1, Ews, po1, outlen1, vb ob1, tk0, 0, 0, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold SS.shim_bounds; rep_lia ]. }
  Intros mf1.
  rewrite alb21_outcome by (auto; lia). simpl fst; simpl snd.
  forward_call (gv, Ews, ps2, str_of a2, Ews, po2, outlen2, vb ob2, tk0, 0, if mf1 then 1 else 0, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold SS.shim_bounds; destruct mf1; rep_lia ]. }
  Intros mf2.
  rewrite alb21_outcome by (auto; lia). simpl fst; simpl snd.
  assert (Hs: SS.str_ok (str_of a1 ++ [46] ++ str_of a2)).
  { unfold SS.str_ok in *. rewrite !Forall_app. repeat split; auto. repeat constructor; rep_lia. }
  forward_call (gv, Ews, pn, str_of a1 ++ [46] ++ str_of a2, Ews, po, outlen1 + outlen2, vb ob, tk0, 0,
                if mf2 then 1 else if mf1 then 1 else 0, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold SS.shim_bounds; destruct mf1, mf2; rep_lia ]. }
  Intros mf3.
  rewrite alb21_outcome by (auto; lia). simpl fst; simpl snd.
  (* if (ossl_shim_zalloc_failed) return 0; *)
  unfold SS.shim_state. rewrite !(alb21_tint_cs SS.CS CS). Intros.
  forward.
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  (* No allocation failed: hand over to piece 25 with the strings of a1 and a2. *)
  destruct mf3; [ discriminate | ]. destruct mf2; [ discriminate | ]. destruct mf1; [ discriminate | ].
  unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS; subst Delta POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (H25 Espec gv (str_of a1) (str_of a2) outlen1 outlen2 ob1 ob2 ob po1 po2 po) ].
  unfold pre25, outbuf. rewrite !alb21_out_buf by (auto; lia). entailer!.
Qed.
