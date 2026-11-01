(* Piece B of the main of harness/rfc_samples.c: the part of the loop body for sample s past the NULL test of
   out, from count = points[s] to free(out) (RsmMainDefs.pieceB_stmt): ossl_punycode_decode on the literal of
   sample s into points[s] code points returns 1, reports points[s] and gives the code points of decoded[]
   (RsmModel.sample_facts), so the check holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainLib.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* The data of the samples stay folded (entailer! would unfold them). *)
Opaque pts dec enc lit_ids start expected.

Lemma pieceB : pieceB_stmt.
Proof.
  intros Espec gv vc s pl po vs H H2 H0 H1 Hp Hpl.
  unfold preB, iter_next, Delta_main, iterB. abbreviate_semax.
  destruct (sample_facts s H) as (Hlit & Hb & Hl & Hd).
  pose proof (Znth_pts_range s H) as Hk. pose proof (start_bound s H) as Hst.
  remember (Znth s pts) as k eqn:Ek.
  assert (Hpk: Znth s (vb pts) = Vint (Int.repr k))
    by (subst k; unfold vb; rewrite Znth_map by (rewrite Zlength_pts; lia); reflexivity).
    forward.
    { match goal with |- context [tc_val _ ?x] => replace x with (Vint (Int.repr k))
        by (rewrite <- Hpk; reflexivity) end.
      entailer!; try (simpl; rep_lia). }
    match goal with |- context [temp _t'11 ?x] => replace x with (Vint (Int.repr k)) by (rewrite <- Hpk; reflexivity) end.
    forward.
    forward.
    match goal with |- context [temp _t'10 ?x] => replace x with pl by (rewrite <- Hp; reflexivity) end.
    rewrite (lit_arr s pl H). Intros.
    rewrite (arr0_tuchar_cs CS PS.CS). rewrite (arr0_tuint_cs C.CS PS.CS).
    forward_call (gv, Ers, pl, enc s, Ews, po, k, vb vs, Tsh, vc).
    { split; [ eapply Forall_impl; [ | exact Hb ]; simpl; intros; rep_lia | rewrite Zlength_vb; auto ]. }
    replace (PS.decode_result (enc s) k (vb vs)) with (1, vb (expected s), k)
      by (subst k; rewrite decode_result_sample; auto; rewrite Zlength_vb; auto).
    cbn [fst snd].
    forward.
    forward_if (temp _t'3 (Vint Int.one)).
    { forward. forward.
      { match goal with |- context [tc_val _ ?x] => replace x with (Vint (Int.repr k))
          by (rewrite <- Hpk; reflexivity) end.
        entailer!; try (simpl; rep_lia). }
      match goal with |- context [temp _t'9 ?x] => replace x with (Vint (Int.repr k)) by (rewrite <- Hpk; reflexivity) end.
      forward. entailer!. }
    { contradiction || discriminate. }
    assert_PROP (field_compatible (tarray tuint 355) [] (gv _decoded)) as Hfc by (unfold decoded_at; entailer!).
    rewrite (decoded_split gv s H). Intros. rewrite <- Ek.
    assert (Hke: Zlength (expected s) = k) by (subst k; apply Zlength_expected; auto).
    rewrite (arr0_tuint_cs PS.CS C.CS _ _ _ po).
    rewrite (arr0_tuint_cs CS C.CS _ _ _ (field_address0 _ _ _)).
    forward_if (temp _t'4 (Vint Int.one)).
    { forward.
      rewrite <- Hke.
      forward_call (Ews, po, expected s, Ers, field_address0 (Tarray tuint 355 noattr) [ArraySubsc (start s)] (gv _decoded), expected s).
      { pose proof (expected_range s). auto. }
      destruct (list_eq_dec Z.eq_dec (expected s) (expected s)) as [_ | E]; [ | contradiction E; reflexivity ].
      forward. rewrite Hke. entailer!. }
    { contradiction || discriminate. }
    forward_call (Int.one).
    forward.
    { match goal with |- context [tc_val _ ?x] => replace x with (Vint (Int.repr k))
        by (rewrite <- Hpk; reflexivity) end.
      entailer!; try (simpl; rep_lia). }
    match goal with |- context [temp _t'6 ?x] => replace x with (Vint (Int.repr k)) by (rewrite <- Hpk; reflexivity) end.
    forward.
    sep_apply (free_pre po k (vb (expected s)) H2 ltac:(lia)).
    forward_call (tarray tuint k, po, gv).
    try rewrite (arr0_tuchar_cs PS.CS CS _ _ _ pl).
    try rewrite (arr0_tuint_cs C.CS CS _ _ _ (field_address0 _ _ _)).
    subst k.
    sep_apply (derives_refl' _ _ (eq_sym (decoded_split gv s H))).
    sep_apply (derives_refl' _ _ (eq_sym (lit_arr s pl H))).
    rewrite <- Hpl.
    sep_apply (derives_refl' _ _ (eq_sym (lits_split gv s H))).
    rewrite (start_succ s H).
    unfold encoded_at, points_at.
    entailer!.
Qed.
