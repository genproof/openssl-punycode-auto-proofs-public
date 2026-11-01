(* Piece 7 of the main of harness/api_decode_capacity.c: count = cap, the first ossl_punycode_decode and its test,
   and the check that the elements from count on keep their values (DcapMainDefs). *)
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

Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.harness.ARDecRange.
Require OpensslPunycode.proof.laws.api_decode_capacity.DcapModel.

(* ossl_punycode_decode's specification moves to the law's compspecs (its arrays are scalars). *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.

(* An array of n unsigned ints cut at k: the first k elements at q, the others at q + 4k. *)
Lemma arr0_split2_ui {cs: compspecs} sh n k (l: list val) q: 0 <= k <= n -> Zlength l = n -> isptr q ->
  arr0 sh tuint n l q |--
  arr0 sh tuint k (sublist 0 k l) q * arr0 sh tuint (n - k) (sublist k n l) (offset_val (4 * k) q).
Proof.
  intros Hk Hl Hq. unfold arr0.
  destruct (Z.eq_dec n 0) as [E|E]; [ rewrite !if_true by lia; rewrite sepcon_emp; auto | ].
  destruct (Z.eq_dec k 0) as [E0|E0].
  { subst k. rewrite if_false by lia. rewrite emp_sepcon, isptr_offset_val_zero by auto.
    rewrite sublist_same by lia. replace (n - 0) with n by lia. auto. }
  destruct (Z.eq_dec (n - k) 0) as [E1|E1].
  { rewrite sepcon_emp. replace k with n by lia. rewrite sublist_same by lia. auto. }
  assert_PROP (field_compatible (tarray tuint n) [] q) as Hfc by entailer!.
  assert (El: l = sublist 0 k l ++ sublist k n l)
    by (rewrite sublist_rejoin by lia; rewrite sublist_same by lia; auto).
  rewrite El at 1.
  change (tarray tuint n) with (Tarray tuint n noattr).
  rewrite (split2_data_at_Tarray_app k n sh tuint (sublist 0 k l) (sublist k n l)) by list_solve.
  rewrite field_address0_offset by auto with field_compatible.
  simpl. rewrite Z.add_0_l, Z.mul_comm. auto.
Qed.

Lemma piece7 : piece10_stmt -> piece7_stmt.
Proof.
  intros H10 Espec gv vc ve vf bs pi c init po ps. unfold pre7, lvars3, T7, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward.
  forward_call (gv, Ews, pi, bs, Ews, po, c, vb init, Tsh, vc).
  { rewrite Zlength_vb; auto. }
  (* Inputs of UINT_MAX octets or more, and failures, return 0 at the test. *)
  destruct (Int.max_unsigned <=? Zlength bs) eqn:EB.
  { unfold PS.decode_result. rewrite EB. simpl fst; simpl snd.
    forward_if (PROP (False) LOCAL () SEP ()). { forward. Exists (Int.repr 0). entailer!. } { discriminate. } }
  assert (Hlt: Zlength bs < Int.max_unsigned) by (apply Z.leb_gt; auto).
  destruct (decode bs c) as [ok out] eqn:HD.
  rewrite (DecModel.decode_result_eq bs c (vb init) ok out Hlt HD). simpl fst; simpl snd.
  destruct ok.
  2: { forward_if (PROP (False) LOCAL () SEP ()). { forward. Exists (Int.repr 0). entailer!. } { discriminate. } }
  forward_if. { discriminate. }
  (* Success with out: at most c code points; the model facts the later checks need. *)
  pose proof (ARDecRange.decode_out_range bs c H (proj1 H1)) as [Hr Hl].
  rewrite HD in Hr, Hl. simpl in Hr, Hl. pose proof (Zlength_nonneg out).
  assert (Hf: dcap_facts bs out).
  { split; [ auto | ]. split; [ lia | ]. split; [ auto | ]. split.
    - apply (DcapModel.decode_cap_enough bs c out (Zlength out) HD). lia.
    - intros Hne. apply (DcapModel.decode_cap_needed bs c out HD Hne). }
  forward.
  forward_if (PROP () LOCAL (temp _t'9 (Vint Int.one); temp _out po; temp _input pi;
      temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
      lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
    SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength out) (vb out) po;
         data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         PS.puny_consts gv; mem_mgr gv; TT)).
  2: { exfalso. lia. }
  { forward. forward. forward.
    set (tl := sublist (Zlength out) c init).
    assert (Etl: Zlength tl = c - Zlength out) by (unfold tl; rewrite Zlength_sublist; lia).
    assert (E1: sublist 0 (Zlength out) (vb out ++ sublist (Zlength out) c (vb init)) = vb out)
      by (rewrite sublist_app1 by (rewrite ?Zlength_vb; lia); rewrite sublist_same by (rewrite ?Zlength_vb; lia);
          auto).
    assert (E2: sublist (Zlength out) c (vb out ++ sublist (Zlength out) c (vb init)) = vb tl).
    { unfold tl, vb. rewrite sublist_map. list_solve. }
    assert (E3: sublist (Zlength out) c (vb init) = vb tl) by (unfold tl, vb; rewrite sublist_map; auto).
    sep_apply (arr0_split2_ui Ews c (Zlength out) (vb out ++ sublist (Zlength out) c (vb init)) po);
      [ lia | unfold vb; list_solve | ].
    sep_apply (arr0_split2_ui Ews c (Zlength out) (vb init) ps); [ lia | rewrite Zlength_vb; lia | ].
    Intros.
    rewrite E1, E2, E3. rewrite <- Etl.
    rewrite !(arr0_tuint_cs CS CM.CS Ews (Zlength tl)).
    forward_call (Ews, offset_val (4 * Zlength out) po, tl, Ews, offset_val (4 * Zlength out) ps, tl).
    { entailer!. rewrite Etl. destruct po; try contradiction; destruct ps; try contradiction. simpl.
      rewrite Int.unsigned_repr by rep_lia. reflexivity. }
    { unfold tl; split; apply Forall_sublist; auto. }
    destruct (list_eq_dec Z.eq_dec tl tl) as [_ | NE]; [ | contradiction NE; reflexivity ].
    forward. entailer!. }
  forward_call (Int.one).
  eapply semax_pre; [ | apply (H10 Espec gv vc ve vf bs pi out po) ].
  unfold pre10, lvars3. entailer!.
Qed.
