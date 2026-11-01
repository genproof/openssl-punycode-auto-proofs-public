(* Piece 18 of the main of harness/api_a2ulabel_labels.c: the copy of s2 into name after the '.', up to its first
   NUL, the NUL of name and the reset of ossl_shim_zalloc_failed (AlbMainDefs). *)
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

Lemma alb18_byte l i: bytes_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= 255.
Proof. intros Hok Hi. unfold bytes_ok in Hok. rewrite Forall_forall in Hok. apply Hok. apply Znth_In; auto. Qed.

Lemma alb18_ok0 l: bytes_ok l -> bytes_ok (l ++ [0]).
Proof. unfold bytes_ok. intros. apply Forall_app. split; auto. constructor; [ rep_lia | constructor ]. Qed.

(* An octet of a buffer, as the value a load of it gives (whatever the default element of Znth). *)
Lemma alb18_vb_at (d: Inhabitant val) l i: 0 <= i < Zlength l -> @Znth val d i (vb l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold vb. rewrite Znth_map by lia. reflexivity. Qed.

(* Every octet before the first NUL is nonzero. *)
Lemma alb18_before0 l i: 0 <= i < first0 l -> Znth i l <> 0.
Proof.
  intros Hi. pose proof (first0_nz l) as Hnz. pose proof (first0_range l).
  unfold str_of in Hnz. rewrite Forall_forall in Hnz.
  replace (Znth i l) with (Znth i (sublist 0 (first0 l) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Hnz. apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

(* The copy of octet j of a right after s '.' and a's first j octets, in a buffer whose rest is undefined. *)
Lemma alb18_step s a j N: 0 <= j < Zlength a -> j < N ->
  upd_Znth (Zlength s + 1 + j) (vb (s ++ [46] ++ sublist 0 j a) ++ Zrepeat Vundef (N - j))
    (Vint (Int.repr (Znth j a))) =
  vb (s ++ [46] ++ sublist 0 (j + 1) a) ++ Zrepeat Vundef (N - (j + 1)).
Proof. intros. unfold vb. list_solve. Qed.

(* The NUL stored right after s '.' t. *)
Lemma alb18_nul s t M: 1 <= M ->
  upd_Znth (Zlength s + 1 + Zlength t) (vb (s ++ [46] ++ t) ++ Zrepeat Vundef M)
    (Vint (Int.zero_ext 8 (Int.repr 0))) =
  vb (s ++ [46] ++ t ++ [0]) ++ Zrepeat Vundef (M - 1).
Proof. intros. change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). unfold vb. list_solve. Qed.

Lemma alb18_tint (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma piece18 : piece21_stmt -> piece18_stmt.
Proof.
  intros H21 Espec gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po.
  unfold pre18, T18. abbreviate_semax.
  Intros.
  pose proof (first0_range a1). pose proof (first0_range a2).
  assert (Zlength (str_of a1) = first0 a1) as Hs1 by (unfold str_of; rewrite Zlength_sublist by lia; lia).
  assert (Zlength (a2 ++ [0]) = len2 + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  pose proof (alb18_ok0 a2 ltac:(assumption)).
  forward_loop
    (EX j: Z,
     PROP (0 <= j <= first0 a2)
     LOCAL (temp _n2 (Vlong (Int64.repr j)); temp _n1 (Vlong (Int64.repr (first0 a1)));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (str_of a1 ++ [46] ++ sublist 0 j a2) ++ Zrepeat Vundef (len1 + len2 + 1 - first0 a1 - j)) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT))
  continue:
    (EX j: Z,
     PROP (0 <= j < first0 a2)
     LOCAL (temp _n2 (Vlong (Int64.repr j)); temp _n1 (Vlong (Int64.repr (first0 a1)));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (str_of a1 ++ [46] ++ sublist 0 (j + 1) a2) ++
             Zrepeat Vundef (len1 + len2 + 1 - first0 a1 - (j + 1))) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT))
  break:
    (PROP ()
     LOCAL (temp _n2 (Vlong (Int64.repr (first0 a2))); temp _n1 (Vlong (Int64.repr (first0 a1)));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (str_of a1 ++ [46] ++ str_of a2) ++ Zrepeat Vundef (len1 + len2 + 1 - first0 a1 - first0 a2)) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT)).
  - Exists 0. rewrite sublist_nil, Z.sub_0_r. change ([46] ++ @nil Z) with [46]. entailer!.
  - Intros j. forward.
    + assert (0 <= Znth j (a2 ++ [0]) <= 255) by (apply alb18_byte; auto; lia).
      entailer!. rewrite alb18_vb_at by lia.
      simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
    + rewrite alb18_vb_at by lia. forward_if.
      * assert (j < first0 a2).
        { destruct (Z.eq_dec j (first0 a2)); [ | lia ]. subst j. rewrite first0_at in H18. contradiction. }
        rewrite app_Znth1 by lia.
        forward.
        { entailer!. rewrite alb18_vb_at by lia. rewrite app_Znth1 by lia. assumption. }
        rewrite alb18_vb_at by lia. rewrite app_Znth1 by lia.
        forward.
        assert (0 <= Znth j a2 <= 255) by (apply alb18_byte; auto; lia).
        rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
        replace (first0 a1 + 1 + j) with (Zlength (str_of a1) + 1 + j) by lia.
        rewrite (alb18_step (str_of a1) a2 j (len1 + len2 + 1 - first0 a1)) by lia.
        Exists j. entailer!.
      * assert (j = first0 a2).
        { assert (0 <= Znth j (a2 ++ [0]) <= 255) by (apply alb18_byte; auto; lia).
          apply repr_inj_unsigned in H18; [ | rep_lia | rep_lia ].
          destruct (Z.eq_dec j (first0 a2)); [ assumption | ].
          rewrite app_Znth1 in H18 by lia. exfalso. apply (alb18_before0 a2 j); [ lia | assumption ]. }
        subst j. unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold main_post. abbreviate_semax.
        forward. unfold str_of at 2. entailer!.
  - Intros j. forward. Exists (j + 1). entailer!.
  - forward.
    assert (Zlength (str_of a2) = first0 a2) as Hs2 by (unfold str_of; rewrite Zlength_sublist by lia; lia).
    replace (first0 a1 + 1 + first0 a2) with (Zlength (str_of a1) + 1 + Zlength (str_of a2)) by lia.
    rewrite (alb18_nul (str_of a1) (str_of a2)) by lia.
    unfold SS.shim_state. Intros.
    rewrite !(alb18_tint SS.CS CS).
    forward.
    replace (len1 + len2 + 1 - first0 a1 - first0 a2 - 1) with (len1 + len2 - first0 a1 - first0 a2) by lia.
    unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS. subst Delta POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (H21 Espec gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po) ].
    unfold pre21, SS.shim_state. rewrite !(alb18_tint SS.CS CS). entailer!.
Qed.
