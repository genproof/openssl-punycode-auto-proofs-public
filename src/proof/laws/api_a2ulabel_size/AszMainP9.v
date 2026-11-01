(* Piece 9 of the main of harness/api_a2ulabel_size.c (AszMainDefs): the two calls of ossl_a2ulabel on the string of
   in (its octets up to the first NUL), into big and into out, and the test of the shim's failure flag and of the
   first result. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszStr.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszFacts.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainDefs.
Local Open Scope logic.

(* The input array = the string (its octets up to the first NUL, with the NUL), then the rest. *)
Lemma in_split_first0 len bs pin:
  Zlength bs = len ->
  data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin =
  (OpensslPunycode.proof.shim.ShimSpec.cstr Ews (sublist 0 (first0 bs) bs) pin *
   data_at Ews (tarray tuchar (len - first0 bs)) (vb (sublist (first0 bs + 1) (len + 1) (bs ++ [0])))
     (field_address0 (tarray tuchar (len + 1)) (SUB (first0 bs + 1)) pin))%logic.
Proof.
  intros Hlen. pose proof (first0_range bs).
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite (first0_split bs) at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (first0 bs + 1)).
  - replace (len + 1 - (first0 bs + 1)) with (len - first0 bs) by lia.
    replace (Zlength (sublist 0 (first0 bs) bs) + 1) with (first0 bs + 1) by list_solve. subst len. reflexivity.
  - list_solve.
  - list_solve.
Qed.

Lemma data_at_tint_csA (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma piece9 : piece12_stmt -> piece9_stmt.
Proof.
  intros H12 Espec gv len bs pin biglen pbig bb outlen pout ob.
  unfold pre9, T9, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite (in_split_first0 len bs pin) by auto. Intros.
  set (s := sublist 0 (first0 bs) bs).
  assert (Hs: OpensslPunycode.proof.shim.ShimSpec.str_ok s) by (apply first0_str; auto).
  (* r1 = ossl_a2ulabel(in, big, biglen) *)
  forward_call (gv, Ews, pin, s, Ews, pbig, biglen, vb bb, tk0, 0, 0, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds; rep_lia ]. }
  Intros mf1.
  remember (OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pbig biglen s (vb bb) 0 0 mf1) as oc1 eqn:E1.
  destruct oc1 as [[[r1 fn1] zf1] ov1]. symmetry in E1. simpl.
  destruct (asz_outcome _ _ _ _ _ _ _ _ _ _ H8 E1) as [-> [Hr1 [Hz1 [Hok1 H01]]]].
  (* r = ossl_a2ulabel(in, out, outlen) *)
  forward_call (gv, Ews, pin, s, Ews, pout, outlen, vb ob, tk0, 0, zf1, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds; rep_lia ]. }
  Intros mf2.
  remember (OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pout outlen s (vb ob) 0 zf1 mf2) as oc2 eqn:E2.
  destruct oc2 as [[[r2 fn2] zf2] ov2]. symmetry in E2. simpl.
  destruct (asz_outcome _ _ _ _ _ _ _ _ _ _ H9 E2) as [-> [Hr2 [Hz2 [Hok2 H02]]]].
  assert (Hz2': zf2 = 0 \/ zf2 = 1) by (destruct Hz2 as [-> | ->]; auto).
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite (data_at_tint_csA OpensslPunycode.proof.shim.ShimSpec.CS CS Ews (Vint (Int.repr zf2))). Intros.
  forward.
  destruct Hz2' as [Ez | Ez]; subst zf2.
  2: {
    forward_if (temp _t'12 (Vint Int.one)).
    { forward. entailer!. }
    { first [ discriminate | contradiction ]. }
    forward_if False.
    { forward. Exists (Int.repr 0). entailer!. }
    { first [ discriminate | contradiction ]. }
  }
  destruct (Hok2 eq_refl ltac:(lia)) as [-> [Er2 Eov2]]. clear Hok2 Hz2 Hz1.
  destruct (Z.eq_dec r1 1) as [Er1 | Nr1].
  2: {
    forward_if (temp _t'12 (Vint Int.one)).
    { first [ discriminate | contradiction ]. }
    { forward. entailer!. destruct Hr1 as [-> | [-> | ->]]; [ reflexivity | reflexivity | contradiction ]. }
    forward_if False.
    { forward. Exists (Int.repr 0). entailer!. }
    { first [ discriminate | contradiction ]. }
  }
  subst r1.
  assert (Hb0: biglen <> 0) by (intros E; specialize (H01 E); discriminate).
  destruct (Hok1 eq_refl Hb0) as [_ [Er1 Eov1]]. clear Hok1 H01 Hr1 Hr2.
  forward_if (temp _t'12 (Vint Int.zero)).
  { first [ discriminate | contradiction ]. }
  { forward. entailer!. }
  forward_if True.
  { first [ discriminate | contradiction ]. }
  { forward. entailer!. }
  destruct (a2ulabel s biglen) as [r1' w] eqn:EA1. simpl in Er1, Eov1. subst r1'.
  destruct (a2ulabel s outlen) as [r2x w2] eqn:EA2. simpl in Eov2.
  destruct (asz_after s biglen outlen r2x w2 w (sublist (Zlength w2) outlen (vb ob)) Hs ltac:(lia) ltac:(lia)
              EA1 EA2) as [w' [-> [F [Hl [Hfit Hshort]]]]].
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  simpl in Er2. subst r2.
  destruct (Val.eq pbig nullval); [ contradiction | ]. destruct (Val.eq pout nullval); [ contradiction | ].
  destruct (Z.eq_dec outlen 0); [ lia | ]. destruct (Z.eq_dec biglen 0); [ lia | ].
  eapply semax_pre;
    [ | apply (H12 Espec gv biglen pbig w' (sublist (Zlength (w' ++ [0])) biglen (vb bb)) outlen pout ov2 r2x) ].
  unfold pre12. subst ov1 ov2.
  rewrite !(data_at_tuchar_cs OpensslPunycode.proof.punycode.PunySpec.CS CS).
  entailer!.
Qed.
