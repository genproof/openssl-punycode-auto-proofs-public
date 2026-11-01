(* Piece 12 of the main of harness/api_a2ulabel_labels.c: the NULs at the ends of s1 and s2, n1 = n2 = 0, the copy
   of s1 into name up to its first NUL, then the '.' (AlbMainDefs). *)
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

(* The NUL stored at the end of a buffer of n + 1 octets: the buffer then holds its first n octets and the NUL. *)
Lemma alb12_nul bs n: 0 <= n -> Zlength bs = n + 1 ->
  upd_Znth n (vb bs) (Vint (Int.zero_ext 8 (Int.repr 0))) = vb (sublist 0 n bs ++ [0]).
Proof.
  intros Hn HL. change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
  unfold vb. rewrite (upd_Znth_map (fun b => Vint (Int.repr b)) n bs 0). f_equal. list_solve.
Qed.

(* Every octet before the first NUL is nonzero. *)
Lemma alb12_before0 l i: 0 <= i < first0 l -> Znth i l <> 0.
Proof.
  intros Hi. pose proof (first0_nz l) as Hnz. pose proof (first0_range l).
  unfold str_of in Hnz. rewrite Forall_forall in Hnz.
  replace (Znth i l) with (Znth i (sublist 0 (first0 l) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Hnz. apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

(* An octet of a buffer, as the value a load of it gives (whatever the default element of Znth). *)
Lemma alb12_vb_at (d: Inhabitant val) l i: 0 <= i < Zlength l -> @Znth val d i (vb l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold vb. rewrite Znth_map by lia. reflexivity. Qed.

Lemma alb12_byte l i: bytes_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= 255.
Proof. intros Hok Hi. unfold bytes_ok in Hok. rewrite Forall_forall in Hok. apply Hok. apply Znth_In; auto. Qed.

Lemma alb12_ok0 l: bytes_ok l -> bytes_ok (l ++ [0]).
Proof. unfold bytes_ok. intros. apply Forall_app. split; auto. constructor; [ rep_lia | constructor ]. Qed.

(* The copy of octet i of a into a buffer that held a's first i octets then undefined octets. *)
Lemma alb12_step a i N: 0 <= i < Zlength a -> i < N ->
  upd_Znth i (vb (sublist 0 i a) ++ Zrepeat Vundef (N - i)) (Vint (Int.repr (Znth i a))) =
  vb (sublist 0 (i + 1) a) ++ Zrepeat Vundef (N - (i + 1)).
Proof. intros. unfold vb. list_solve. Qed.

(* The '.' stored right after the string s in a buffer that held s then undefined octets. *)
Lemma alb12_dot s N: Zlength s < N ->
  upd_Znth (Zlength s) (vb s ++ Zrepeat Vundef (N - Zlength s)) (Vint (Int.zero_ext 8 (Int.repr 46))) =
  vb (s ++ [46]) ++ Zrepeat Vundef (N - 1 - Zlength s).
Proof. intros. change (Int.zero_ext 8 (Int.repr 46)) with (Int.repr 46). unfold vb. list_solve. Qed.

Lemma piece12 : piece18_stmt -> piece12_stmt.
Proof.
  intros H18 Espec gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po.
  unfold pre12, T12. abbreviate_semax.
  Intros.
  forward. forward.
  rewrite (alb12_nul bs1 len1) by lia. rewrite (alb12_nul bs2 len2) by lia.
  set (a1 := sublist 0 len1 bs1). set (a2 := sublist 0 len2 bs2).
  assert (Zlength a1 = len1) by (unfold a1; rewrite Zlength_sublist by lia; lia).
  assert (Zlength a2 = len2) by (unfold a2; rewrite Zlength_sublist by lia; lia).
  assert (bytes_ok a1) by (unfold a1, bytes_ok in *; apply Forall_sublist; auto).
  assert (bytes_ok a2) by (unfold a2, bytes_ok in *; apply Forall_sublist; auto).
  clearbody a1 a2.
  assert (Zlength (a1 ++ [0]) = len1 + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  pose proof (alb12_ok0 a1 ltac:(assumption)).
  forward. forward.
  pose proof (first0_range a1).
  change (data_at_ Ews (tarray tuchar (len1 + len2 + 2)) pn) with
    (data_at Ews (tarray tuchar (len1 + len2 + 2)) (Zrepeat Vundef (len1 + len2 + 2)) pn).
  forward_loop
    (EX i: Z,
     PROP (0 <= i <= first0 a1)
     LOCAL (temp _n2 (Vlong (Int64.repr 0)); temp _n1 (Vlong (Int64.repr i));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (sublist 0 i a1) ++ Zrepeat Vundef (len1 + len2 + 2 - i)) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT))
  continue:
    (EX i: Z,
     PROP (0 <= i < first0 a1)
     LOCAL (temp _n2 (Vlong (Int64.repr 0)); temp _n1 (Vlong (Int64.repr i));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (sublist 0 (i + 1) a1) ++ Zrepeat Vundef (len1 + len2 + 2 - (i + 1))) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT))
  break:
    (PROP ()
     LOCAL (temp _n2 (Vlong (Int64.repr 0)); temp _n1 (Vlong (Int64.repr (first0 a1)));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
            temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
     SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
          data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
          data_at Ews (tarray tuchar (len1 + len2 + 2))
            (vb (str_of a1) ++ Zrepeat Vundef (len1 + len2 + 2 - first0 a1)) pn;
          data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
          PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT)).
  - Exists 0. rewrite sublist_nil, Z.sub_0_r. change (vb []) with (@nil val). rewrite app_nil_l. entailer!.
  - Intros i. forward.
    + assert (0 <= Znth i (a1 ++ [0]) <= 255) by (apply alb12_byte; auto; lia).
      entailer!. rewrite alb12_vb_at by lia.
      simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
    + rewrite alb12_vb_at by lia. forward_if.
      * assert (i < first0 a1).
        { destruct (Z.eq_dec i (first0 a1)); [ | lia ]. subst i. rewrite first0_at in H22. contradiction. }
        rewrite app_Znth1 by lia.
        forward.
        { entailer!. rewrite alb12_vb_at by lia. rewrite app_Znth1 by lia. assumption. }
        rewrite alb12_vb_at by lia. rewrite app_Znth1 by lia.
        forward.
        assert (0 <= Znth i a1 <= 255) by (apply alb12_byte; auto; lia).
        rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
        rewrite alb12_step by lia.
        Exists i. entailer!.
      * assert (i = first0 a1).
        { assert (0 <= Znth i (a1 ++ [0]) <= 255) by (apply alb12_byte; auto; lia).
          apply repr_inj_unsigned in H22; [ | rep_lia | rep_lia ].
          destruct (Z.eq_dec i (first0 a1)); [ assumption | ].
          rewrite app_Znth1 in H22 by lia. exfalso. apply (alb12_before0 a1 i); [ lia | assumption ]. }
        subst i. unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold main_post. abbreviate_semax.
        forward. unfold str_of. entailer!.
  - Intros i. forward. Exists (i + 1). entailer!.
  - forward.
    assert (Zlength (str_of a1) = first0 a1) by (unfold str_of; rewrite Zlength_sublist by lia; lia).
    rewrite <- H21. rewrite alb12_dot by lia. rewrite H21.
    replace (len1 + len2 + 2 - 1 - first0 a1) with (len1 + len2 + 1 - first0 a1) by lia.
    unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS. subst Delta POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (H18 Espec gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po) ].
    unfold pre18. entailer!.
Qed.
