(* Piece 15 of the main of harness/rfc_ace_any_case.c: the reset of the failure flag, r1 = ossl_a2ulabel(any_case,
   out1, outlen), failed1 and the second reset (RacMainDefs). *)
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
Local Open Scope logic.

#[local] Instance rac15_cce1 : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance rac15_cce2 : change_composite_env CS PS.CS := CCE_any _ _.

(* The shim's scalars are the same predicates at any compspecs. *)
Lemma rac15_tint_cs (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma rac15_tlong_cs (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tlong v q = @data_at cs2 sh tlong v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* out1's array and the zero-size token are ossl_a2ulabel's output buffer (out1 is not NULL). *)
Lemma rac15_out_buf n v tk q: q <> nullval ->
  @data_at CS Ews (tarray tuchar n) v q * SS.zero_tok n tk q = PS.out_buf Ews q n v tk.
Proof.
  intros Hq. unfold PS.out_buf. rewrite if_false by auto.
  try rewrite (data_at_tuchar_cs PS.CS CS). reflexivity.
Qed.

(* With the knob 0, the call leaves the knob 0. *)
Lemma rac15_knob out cap s ob mf: snd (fst (fst (outc out cap s ob mf))) = 0.
Proof.
  unfold outc, PS.a2u_outcome.
  destruct (Val.eq out nullval); [ reflexivity | ]. destruct (cap =? 0); [ reflexivity | ]. simpl.
  destruct mf; [ reflexivity | ]. destruct (a2ulabel s cap); reflexivity.
Qed.

Lemma piece15 : piece19_stmt -> piece15_stmt.
Proof.
  intros HK Espec gv len a b t outlen ob pa pl po1 po2.
  unfold pre15, T15, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. subst len.
  unfold SS.shim_state.
  rewrite !(rac15_tint_cs SS.CS CS). rewrite !(rac15_tlong_cs SS.CS CS).
  Intros.
  forward.
  gather_SEP 10 11 12.
  replace_SEP 0 (SS.shim_state gv 0 0 0).
  { entailer!. unfold SS.shim_state.
    rewrite !(rac15_tint_cs SS.CS CS). rewrite !(rac15_tlong_cs SS.CS CS). cancel. }
  rewrite (rac_str_split Ews a b t pa). Intros.
  rewrite (rac_tok_split outlen po1). Intros.
  gather_SEP (data_at _ (tarray tuchar outlen) (vb ob) po1) (SS.zero_tok outlen (tarray tuchar 0) po1).
  rewrite (rac15_out_buf outlen (vb ob) (tarray tuchar 0) po1) by auto.
  forward_call (gv, Ews, pa, rstr a b t, Ews, po1, outlen, vb ob, tarray tuchar 0, 0, 0, 0).
  { split; [ apply rstr_ok; auto | ]. split; [ right; unfold vb; rewrite Zlength_map; auto | ].
    unfold SS.shim_bounds. rep_lia. }
  Intros mf.
  change (PS.a2u_outcome po1 outlen (rstr a b t) (vb ob) 0 0 mf) with (outc po1 outlen (rstr a b t) ob mf).
  rewrite rac15_knob.
  rewrite <- (rac15_out_buf outlen _ (tarray tuchar 0) po1) by auto.
  Intros.
  unfold SS.shim_state.
  rewrite !(rac15_tint_cs SS.CS CS). rewrite !(rac15_tlong_cs SS.CS CS).
  Intros.
  forward. forward.
  eapply semax_pre; [ | apply (HK Espec gv (Zlength t) a b t outlen ob pa pl po1 po2 mf) ].
  unfold pre19. rewrite (rac_str_split Ews a b t pa). rewrite (rac_tok_split outlen po1).
  unfold SS.shim_state. rewrite !(rac15_tint_cs SS.CS CS). rewrite !(rac15_tlong_cs SS.CS CS).
  entailer!.
  destruct (Z.eq_dec (Zlength ob) 0); cancel.
Qed.
