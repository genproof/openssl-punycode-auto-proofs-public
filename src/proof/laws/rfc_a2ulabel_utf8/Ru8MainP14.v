(* A piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): count = 512, the call
   ossl_punycode_decode(label + 4, len, cps, &count) and size = 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.

Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* The label "xn--" ++ s ++ NUL cut into the prefix, the len octets of s that the decoder reads at label + 4 (nothing
   when len = 0) and the final NUL. *)
Lemma ru8_label_split: forall len s pl,
  Zlength s = len -> field_compatible (tarray tuchar (len + 5)) [] pl ->
  data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl =
  data_at Ews (tarray tuchar 4) (vb xn) pl * arr0 Ews tuchar len (vb s) (offset_val 4 pl) *
  data_at Ews (tarray tuchar 1) (vb [0]) (offset_val (4 + len) pl).
Proof.
  intros len s pl HL FC.
  assert (Hp: isptr pl) by (destruct FC; auto).
  pose proof (Zlength_nonneg s).
  rewrite !vb_app.
  rewrite (split2_data_at_Tarray_app 4 (len + 5) Ews tuchar (vb xn) (vb s ++ vb [0]) pl)
    by (rewrite ?Zlength_app, ?Zlength_vb; unfold xn; rewrite ?Zlength_cons, ?Zlength_nil; lia).
  rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia).
  replace (len + 5 - 4) with (len + 1) by lia.
  assert (FC2: field_compatible (tarray tuchar (len + 1)) [] (offset_val 4 pl)).
  { pose proof FC as F. rewrite field_compatible_Tarray_split with (i := 4) in F by lia. destruct F as [_ F].
    rewrite field_address0_offset in F by (apply arr_field_compatible0; auto; lia).
    replace (len + 5 - 4) with (len + 1) in F by lia. exact F. }
  rewrite (split2_data_at_Tarray_app len (len + 1) Ews tuchar (vb s) (vb [0]) (offset_val 4 pl))
    by (rewrite ?Zlength_app, ?Zlength_vb; unfold xn; rewrite ?Zlength_cons, ?Zlength_nil; lia).
  rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia).
  replace (len + 1 - len) with 1 by lia.
  simpl nested_field_offset. rewrite offset_offset_val.
  replace (4 + (0 + 1 * len)) with (4 + len) by lia.
  rewrite sepcon_assoc. f_equal. f_equal.
  unfold arr0. destruct (Z.eq_dec len 0); [ | reflexivity ].
  subst len. rewrite Zlength_nil_inv with (l := s) by auto. simpl.
  apply data_at_zero_array_eq; auto.
Qed.

Lemma piece14 : piece17_stmt -> piece14_stmt.
Proof.
  intros HK Espec gv vc len s pl pc outlen ob pout psaved pw.
  unfold pre14, T14, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward.
  assert_PROP (field_compatible (tarray tuchar (len + 5)) [] pl) as FC by entailer!.
  assert (Hp: isptr pl) by (destruct FC; auto).
  rewrite (ru8_label_split len s pl) by auto. Intros.
  rewrite (arr0_tuchar_cs CS PS.CS _ _ _ (offset_val 4 pl)).
  replace (data_at Ews (tarray tuint 512) (Zrepeat Vundef 512) pc)
    with (@arr0 PS.CS Ews tuint 512 (Zrepeat Vundef 512) pc) by (unfold arr0; simpl; apply data_at_tuint_cs).
  subst len.
  forward_call (gv, Ews, offset_val 4 pl, s, Ews, pc, 512, Zrepeat Vundef 512, Tsh, vc).
  change (PS.decode_result s 512 (Zrepeat Vundef 512)) with (dres s).
  (* The decoder returns 1 or 0. *)
  assert (Hr: fst (fst (dres s)) = 0 \/ fst (fst (dres s)) = 1).
  { unfold dres, PS.decode_result. destruct (Int.max_unsigned <=? Zlength s); [ left; reflexivity | ].
    destruct (decode s 512) as [[|] ?]; simpl; auto. }
  forward.
  forward.
  unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS; subst Delta POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (HK Espec gv vc (Zlength s) s pl pc outlen ob pout psaved pw) ].
  unfold pre17.
  rewrite (ru8_label_split (Zlength s) s pl) by auto.
  try rewrite (arr0_tuchar_cs PS.CS CS _ _ _ (offset_val 4 pl)).
  entailer!.
  - destruct Hr as [-> | ->]; reflexivity.
  - unfold arr0. destruct (Z.eq_dec 512 0); [ lia | ]. try rewrite (data_at_tuint_cs PS.CS CS). cancel.
Qed.
