(* Piece 19 of the main of harness/rfc_ace_any_case.c: r2 = ossl_a2ulabel(lower, out2, outlen), the test of the
   failure flags, the check r1 == r2 && bytes_eq(out1, out2, outlen) and the return (RacMainDefs). *)
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

(* ossl_a2ulabel's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* The scalar globals of the shim do not depend on the compspecs. *)
Lemma rac19_tint_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma rac19_tlong_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* After a call with the failure flag 0, the flag is 0 or 1. *)
Lemma rac19_flag po cap s ob mf: snd (fst (outc po cap s ob mf)) = 0 \/ snd (fst (outc po cap s ob mf)) = 1.
Proof.
  unfold outc, PS.a2u_outcome.
  destruct (Val.eq po nullval); [ auto | ]. destruct (cap =? 0); [ auto | ]. simpl.
  destruct mf; [ auto | ]. destruct (a2ulabel s cap); auto.
Qed.

(* out2's block as ossl_a2ulabel's output buffer (with the zero-size token it wants) and the rest of its token. *)
Lemma rac19_out_buf n ob p: p <> nullval ->
  @malloc_token HelperSpec.CS Ews (tarray tuchar n) p * @data_at CS Ews (tarray tuchar n) (vb ob) p |--
  PS.out_buf Ews p n (vb ob) (tarray tuchar 0) *
  (if Z.eq_dec n 0 then emp else @malloc_token HelperSpec.CS Ews (tarray tuchar n) p).
Proof.
  intros Hp. rewrite (rac_tok_split n p) at 1. unfold PS.out_buf.
  destruct (Val.eq p nullval); [ contradiction | ].
  rewrite (data_at_tuchar_cs CS PS.CS). cancel.
Qed.

(* A byte array as the array bytes_eq reads (none when its size is 0) and what is left of it. *)
Lemma rac19_arr0 sh n v p:
  @data_at CS sh (tarray tuchar n) v p =
  @arr0 HelperSpec.CS sh tuchar n v p * (if Z.eq_dec n 0 then @data_at CS sh (tarray tuchar n) v p else emp).
Proof.
  unfold arr0. destruct (Z.eq_dec n 0).
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. apply data_at_tuchar_cs.
Qed.

Lemma piece19 : piece19_stmt.
Proof.
  intros Espec gv len a b t outlen ob pa pl po1 po2 mf1.
  unfold pre19, T19, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. subst len.
  rewrite (rac_str_split Ews 120 110 t pl). Intros.
  sep_apply (rac19_out_buf outlen ob po2 H10). Intros.
  forward_call (gv, Ews, pl, rstr 120 110 t, Ews, po2, outlen, vb ob, tarray tuchar 0, 0, 0, 0).
  { split; [ apply rstr_ok; auto | split; [ right; unfold vb; rewrite Zlength_map; auto | ] ].
    unfold ShimSpec.shim_bounds. rep_lia. }
  Intros mf2.
  fold (outc po2 outlen (rstr 120 110 t) ob mf2).
  unfold ShimSpec.shim_state.
  rewrite !(rac19_tint_cs ShimSpec.CS CS). rewrite !(rac19_tlong_cs ShimSpec.CS CS).
  Intros.
  forward.
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  assert (E: snd (fst (outc po1 outlen (rstr a b t) ob mf1)) =
             snd (fst (outc po2 outlen (rstr 120 110 t) ob mf2))).
  { destruct (rac19_flag po1 outlen (rstr a b t) ob mf1) as [E1 | E1],
      (rac19_flag po2 outlen (rstr 120 110 t) ob mf2) as [E2 | E2];
      rewrite E1, E2 in *; auto;
      apply (f_equal Int.unsigned) in H0; rewrite !Int.unsigned_repr in H0 by rep_lia; lia. }
  destruct (rac_outcome po1 po2 outlen a b t ob mf1 mf2 H9 H10 H2 H3 E) as [Er Eb].
  rewrite Er, Eb.
  unfold PS.out_buf. destruct (Val.eq po2 nullval); [ contradiction | ].
  rewrite (data_at_tuchar_cs PS.CS CS). Intros.
  assert_PROP (exists L, bytes_ok L /\ snd (outc po2 outlen (rstr 120 110 t) ob mf2) = vb L) as HL.
  { sep_apply (rac_vb_fits Ews outlen _ po1 (rac_outcome_ints po2 outlen (rstr 120 110 t) ob mf2)). entailer!. }
  destruct HL as [L [HL EL]]. rewrite EL.
  assert_PROP (Zlength L = outlen) as HZ.
  { entailer!. unfold vb in *. rewrite Zlength_map in *. auto. }
  rewrite <- HZ in *.
  forward_if (temp _t'15 (Vint Int.one)).
  { rewrite (rac19_arr0 Ews (Zlength L) (vb L) po1), (rac19_arr0 Ews (Zlength L) (vb L) po2). Intros.
    forward_call (Ews, po1, L, Ews, po2, L).
    destruct (list_eq_dec Z.eq_dec L L) as [_ | NE]; [ | contradiction NE; reflexivity ].
    forward. entailer!.
    unfold arr0; destruct (Z.eq_dec (Zlength L) 0); rewrite ?(data_at_tuchar_cs HelperSpec.CS CS); cancel. }
  { contradiction || discriminate || (rewrite Int.eq_true in *; discriminate). }
  forward_call (Int.one).
  forward. Exists (Int.repr 0). entailer!.
Qed.
