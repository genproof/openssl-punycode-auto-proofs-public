(* Piece 9 of the main of harness/rfc_digit_case.c: count1 = count2 = cap, the two calls of ossl_punycode_decode
   (on input and on other) and the two checks (RdcMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.harness.ARDecRange.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcModel.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* What the two calls give, as the checks need it: the same result and count; on result 1 both arrays start with
   the same code points out (count = |out| <= cap, each an unsigned int), followed by what was there before. *)
Lemma rdc_results bs bs' cap i1 i2:
  bytes_ok bs -> case_rel (delta_start bs) bs bs' -> 0 <= cap ->
  fst (fst (PS.decode_result bs' cap i2)) = fst (fst (PS.decode_result bs cap i1)) /\
  snd (PS.decode_result bs' cap i2) = snd (PS.decode_result bs cap i1) /\
  (fst (fst (PS.decode_result bs cap i1)) = 0 \/
   fst (fst (PS.decode_result bs cap i1)) = 1 /\
   exists out, Zlength out <= cap /\ Forall (fun x => 0 <= x <= Int.max_unsigned) out /\
     snd (PS.decode_result bs cap i1) = Zlength out /\
     snd (fst (PS.decode_result bs cap i1)) = vb out ++ sublist (Zlength out) cap i1 /\
     snd (fst (PS.decode_result bs' cap i2)) = vb out ++ sublist (Zlength out) cap i2).
Proof.
  intros OK R Hc. pose proof (decode_case bs bs' cap R) as Hd. destruct R as [HL _].
  pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range bs cap OK Hc) as [Hr Hl].
  unfold PS.decode_result. rewrite HL, Hd.
  destruct (Int.max_unsigned <=? Zlength bs); [ simpl; auto | ].
  destruct (decode bs cap) as [ok out]. simpl in Hr, Hl.
  destruct ok; simpl; [ | auto ].
  split; [ reflexivity | split; [ reflexivity | right; split; [ reflexivity | ] ] ].
  exists out. repeat split; auto.
Qed.

(* An array of cap unsigned ints starting with out holds out at its start. *)
Lemma rdc_arr_prefix {cs: compspecs} sh cap (out: list Z) rest p:
  Zlength out <= cap -> Zlength rest = cap - Zlength out ->
  arr0 sh tuint cap (vb out ++ rest) p |-- arr0 sh tuint (Zlength out) (vb out) p * TT.
Proof.
  intros H1 H2. pose proof (Zlength_nonneg out). unfold arr0.
  destruct (Z.eq_dec (Zlength out) 0) as [E | E].
  - destruct (Z.eq_dec cap 0); cancel.
  - destruct (Z.eq_dec cap 0); [ lia | ].
    rewrite (split2_data_at_Tarray_app (Zlength out) cap sh tuint (vb out) rest p);
      [ cancel | unfold vb; rewrite Zlength_map; reflexivity | exact H2 ].
Qed.

Lemma piece9 : piece9_stmt.
Proof.
  intros Espec gv v1 v2 bs bs' pi ps init1 po1 init2 po2. unfold pre9, T9, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  pose proof H1 as [HL _].
  forward. forward.
  rewrite (arr0_tuint_cs CS PS.CS _ _ _ po1). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  forward_call (gv, Ews, pi, bs, Ews, po1, Zlength init1, vb init1, Tsh, v1).
  { unfold vb. apply Zlength_map. }
  rewrite (arr0_tuint_cs CS PS.CS _ _ _ po2). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ ps).
  rewrite <- HL.
  forward_call (gv, Ews, ps, bs', Ews, po2, Zlength init1, vb init2, Tsh, v2).
  { unfold vb. rewrite Zlength_map. lia. }
  pose proof (rdc_results bs bs' (Zlength init1) (vb init1) (vb init2) H H1 (Zlength_nonneg _)) as [Er [Ec Hres]].
  destruct (PS.decode_result bs (Zlength init1) (vb init1)) as [[r1 a1] c1].
  destruct (PS.decode_result bs' (Zlength init1) (vb init2)) as [[r2 a2] c2].
  simpl fst in *; simpl snd in *. subst r2 c2.
  forward_if (temp _t'17 (Vint Int.one)).
  { forward. forward. forward. entailer!. rewrite Int.eq_true. reflexivity. }
  { forward. entailer!. }
  forward_call (Int.one).
  destruct Hres as [-> | [-> [out [Hl [Hrg [-> [-> ->]]]]]]].
  - forward_if True.
    { contradiction || discriminate. }
    { forward. entailer!. }
    forward. Exists (Int.repr 0). entailer!.
  - forward_if (PROP () LOCAL (lvar _count1 tuint v1; lvar _count2 tuint v2)
      SEP (data_at Tsh tuint (Vint (Int.repr (Zlength out))) v1;
           data_at Tsh tuint (Vint (Int.repr (Zlength out))) v2; TT)).
    2: { contradiction || discriminate. }
    { forward. pose proof (Zlength_nonneg out).
      assert (Hs1: Zlength (sublist (Zlength out) (Zlength init1) (vb init1)) = Zlength init1 - Zlength out)
        by (rewrite Zlength_sublist; unfold vb; rewrite ?Zlength_map; lia).
      assert (Hs2: Zlength (sublist (Zlength out) (Zlength init1) (vb init2)) = Zlength init1 - Zlength out)
        by (rewrite Zlength_sublist; unfold vb; rewrite ?Zlength_map; lia).
      sep_apply (rdc_arr_prefix Ews (Zlength init1) out _ po1 Hl Hs1).
      sep_apply (rdc_arr_prefix Ews (Zlength init1) out _ po2 Hl Hs2).
      Intros.
      rewrite (arr0_tuint_cs _ C.CS _ _ _ po1), (arr0_tuint_cs _ C.CS _ _ _ po2).
      forward_call (Ews, po1, out, Ews, po2, out).
      destruct (list_eq_dec Z.eq_dec out out) as [_ | E]; [ | contradiction E; reflexivity ].
      forward_call (Int.one).
      entailer!. }
    forward. Exists (Int.repr 0). entailer!.
Qed.
