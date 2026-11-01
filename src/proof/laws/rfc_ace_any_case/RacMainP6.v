(* Piece 6 of the main of harness/rfc_ace_any_case.c: the writes of the prefix [a; b; '-'; '-'] and the NUL into
   any_case, its copy lower, the NULL test of lower and the writes of "xn" into lower (RacMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_ace_any_case.code.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacModel.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacLib.
Require Import OpensslPunycode.proof.laws.common.CmnLib.
Local Open Scope logic.

Module H := OpensslPunycode.proof.laws.common.HelperSpec.

(* The copy of copy_of, NULL when malloc failed: kept folded in the main (VST's automation is slow on the
   conditional of the unfolded form). *)
Definition rblk (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else @malloc_token H.CS Ews (tarray tuchar n) p * @data_at H.CS Ews (tarray tuchar n) v p.

(* The test p == NULL of such a copy is defined. *)
Lemma rblk_tc_test n v p P:
  0 <= n -> rblk n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold rblk. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - apply (@cmn_malloc_tc_test1 H.CS); auto. simpl. lia.
Qed.

(* copy_of's source in the form of its precondition: the block of any_bytes, its token at the helpers' compspecs. *)
Lemma rac_src p n bs:
  p <> nullval -> Zlength bs = n ->
  @malloc_token H.CS Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (vb bs) p
  |-- if eq_dec p nullval then emp
      else @malloc_token H.CS Ews (tarray tuchar (Zlength bs)) p *
           @data_at H.CS Ews (tarray tuchar (Zlength bs)) (vb bs) p.
Proof.
  intros Hp Hn. subst n. rewrite if_false by auto. rewrite (data_at_tuchar_cs CS H.CS). auto.
Qed.

Lemma piece6 : piece15_stmt -> piece6_stmt.
Proof.
  intros H15 Espec gv len bs outlen ob pa po1 po2. unfold pre6, T6, ret0, main_post, Delta_main.
  abbreviate_semax. Intros.
  forward_call. Intros c0.
  forward_if (temp _t'9 (Vint (Int.repr (if Z.eq_dec c0 0 then 88 else 120)))).
  { forward. entailer!. }
  { forward. entailer!. destruct (Z.eq_dec c0 0); [ lia | reflexivity ]. }
  forward.
  forward_call. Intros c1.
  forward_if (temp _t'11 (Vint (Int.repr (if Z.eq_dec c1 0 then 78 else 110)))).
  { forward. entailer!. }
  { forward. entailer!. destruct (Z.eq_dec c1 0); [ lia | reflexivity ]. }
  forward.
  forward.
  forward.
  forward.
  set (a := if Z.eq_dec c0 0 then 88 else 120).
  set (b := if Z.eq_dec c1 0 then 78 else 110).
  set (t := sublist 4 (len + 4) bs).
  assert (Ha: a = 88 \/ a = 120) by (subst a; destruct (Z.eq_dec c0 0); auto).
  assert (Hb: b = 78 \/ b = 110) by (subst b; destruct (Z.eq_dec c1 0); auto).
  assert (Hza: Int.zero_ext 8 (Int.repr a) = Int.repr a) by (destruct Ha as [-> | ->]; reflexivity).
  assert (Hzb: Int.zero_ext 8 (Int.repr b) = Int.repr b) by (destruct Hb as [-> | ->]; reflexivity).
  rewrite Hza, Hzb. change (Int.zero_ext 8 (Int.repr 45)) with (Int.repr 45).
  change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
  match goal with |- context [data_at Ews (tarray tuchar (len + 5)) ?v pa] =>
    replace v with (vb ([a; b; 45; 45] ++ t ++ [0])) end.
  2: { unfold vb, t. list_solve. }
  assert (Hl: Zlength ([a; b; 45; 45] ++ t ++ [0]) = len + 5) by (unfold t; list_solve).
  assert (Ht: bytes_ok t) by (apply Forall_sublist; auto).
  assert (Hok: bytes_ok ([a; b; 45; 45] ++ t ++ [0])).
  { unfold bytes_ok. apply Forall_app; split; [ | apply Forall_app; split; [ exact Ht | ] ].
    - repeat constructor; rep_lia.
    - repeat constructor; rep_lia. }
  sep_apply (rac_src pa (len + 5) ([a; b; 45; 45] ++ t ++ [0]) H5 Hl).
  forward_call (Ews, pa, [a; b; 45; 45] ++ t ++ [0], len + 5, gv).
  Intros pl. rewrite if_false by auto. rewrite sublist_same by lia.
  fold (rblk (len + 5) (vb ([a; b; 45; 45] ++ t ++ [0])) pl).
  forward_if.
  { apply derives_trans with (rblk (len + 5) (vb ([a; b; 45; 45] ++ t ++ [0])) pl * TT);
      [ cancel | apply rblk_tc_test; lia ]. }
  { forward. Exists (Int.repr 0). entailer!. }
  unfold rblk. rewrite if_false by auto. rewrite Hl. Intros.
  rewrite (data_at_tuchar_cs H.CS CS _ _ _ pa). rewrite (data_at_tuchar_cs H.CS CS _ _ _ pl).
  forward.
  forward.
  change (Int.zero_ext 8 (Int.repr 120)) with (Int.repr 120).
  change (Int.zero_ext 8 (Int.repr 110)) with (Int.repr 110).
  match goal with |- context [data_at Ews (tarray tuchar (len + 5)) ?v pl] =>
    replace v with (vb ([120; 110; 45; 45] ++ t ++ [0])) end.
  2: { unfold vb. list_solve. }
  eapply semax_pre; [ | apply (H15 Espec gv len a b t outlen ob pa pl po1 po2) ].
  unfold pre15. entailer!.
  unfold t. rewrite Zlength_sublist by lia. lia.
Qed.
