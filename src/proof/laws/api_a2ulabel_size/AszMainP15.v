(* Piece 15 of the main of harness/api_a2ulabel_size.c (AszMainDefs): the checks.  size is the number of octets the
   first call wrote; when outlen >= size the second call gave 1 and wrote the same octets, else it gave 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainDefs.
Local Open Scope logic.

Lemma data_at_arr0_nzA (cs1 cs2: compspecs) sh n v q:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v q = @arr0 cs2 sh tuchar n v q.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma bytes_ok_nul w': Forall (fun b => 1 <= b <= 255) w' -> bytes_ok (w' ++ [0]).
Proof.
  intros H. unfold bytes_ok. rewrite Forall_app. split; [ | repeat constructor; rep_lia ].
  eapply Forall_impl; [ | exact H ]. simpl. intros; rep_lia.
Qed.

Lemma piece15 : piece15_stmt.
Proof.
  intros Espec gv biglen pbig w' tb outlen pout ov r.
  unfold pre15, T15, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. pose proof (Zlength_nonneg w').
  forward_if (PROP () LOCAL () SEP (TT)).
  - destruct (H2 ltac:(lia)) as [-> Hov]. clear H2 H3.
    assert_PROP (Zlength ov = outlen) by entailer!.
    assert_PROP (Zlength (vb (w' ++ [0]) ++ tb) = biglen) by (entailer!; rewrite Z.max_r in * by lia; assumption).
    set (w := w' ++ [0]) in *.
    assert (Hw: Zlength w = Zlength w' + 1) by (subst w; list_solve).
    rewrite <- Hw in *.
    forward_if (PROP () LOCAL (temp _t'14 (Vint Int.one)) SEP (TT)).
    + replace ov with (vb w ++ sublist (Zlength w) outlen ov) by (rewrite <- Hov; list_solve).
      rewrite (split2_data_at_Tarray_app (Zlength w) outlen) by list_solve.
      rewrite (split2_data_at_Tarray_app (Zlength w) biglen) by list_solve.
      Intros.
      rewrite (data_at_arr0_nzA CS OpensslPunycode.proof.laws.common.HelperSpec.CS Ews (Zlength w) (vb w) pout)
        by list_solve.
      rewrite (data_at_arr0_nzA CS OpensslPunycode.proof.laws.common.HelperSpec.CS Ews (Zlength w) (vb w) pbig)
        by list_solve.
      forward_call (Ews, pout, w, Ews, pbig, w).
      { pose proof (bytes_ok_nul w' H0). split; auto. }
      destruct (list_eq_dec Z.eq_dec w w) as [_ | E]; [ | contradiction ].
      forward. entailer!.
    + contradiction.
    + forward_call. entailer!.
  - rewrite H3 by lia. clear H2 H3.
    forward_call. entailer!.
  - forward. Exists (Int.repr 0). entailer!.
Qed.
