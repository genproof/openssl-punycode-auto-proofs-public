(* Helpers of MainLab.v (piece_lab): the octets of lab, ulen's bounds, the tail from the NULL tests of u and want to
   piece_utf8. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Local Open Scope logic.

Lemma utf8_len (c: Z): 0 <= Zlength (utf8 c) <= 4.
Proof.
  unfold utf8.
  destruct (c <? 128); [ | destruct (c <? 2048); [ | destruct (c <? 65536); [ | destruct (c <=? 1114111)]]];
    rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma utf8s_len (cps: list Z): 0 <= Zlength (utf8s cps) <= 4 * Zlength cps.
Proof.
  induction cps as [ | c r IH]; unfold utf8s in *; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons. pose proof (utf8_len c). lia.
Qed.

Lemma ulen_of_bounds (cps: list Z): 1 <= ulen_of cps <= 4 * Zlength cps + 1.
Proof. unfold ulen_of. pose proof (utf8s_len cps). lia. Qed.

Lemma lab_ace (m: Z) (e: list Z):
  0 <= Zlength e <= 16 * m + 1 ->
  upd_Znth (4 + Zlength e)
    (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (lab_after_encode m e)
       (Vint (Int.zero_ext 8 (Int.repr 120)))) (Vint (Int.zero_ext 8 (Int.repr 110))))
       (Vint (Int.zero_ext 8 (Int.repr 45)))) (Vint (Int.zero_ext 8 (Int.repr 45))))
    (Vint (Int.zero_ext 8 (Int.repr 0)))
  = vb (ace e ++ [0]) ++ Zrepeat Vundef (16 * m + 1 - Zlength e).
Proof.
  intros Hb. unfold lab_after_encode, ace.
  change (Int.zero_ext 8 (Int.repr 120)) with (Int.repr 120).
  change (Int.zero_ext 8 (Int.repr 110)) with (Int.repr 110).
  change (Int.zero_ext 8 (Int.repr 45)) with (Int.repr 45).
  change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
  replace (Zrepeat Vundef (16 * m + 2 - Zlength e)) with (Vundef :: Zrepeat Vundef (16 * m + 1 - Zlength e)).
  2: { unfold Zrepeat. replace (Z.to_nat (16 * m + 2 - Zlength e)) with (S (Z.to_nat (16 * m + 1 - Zlength e)))
         by lia. reflexivity. }
  change (Zrepeat Vundef 4) with [Vundef; Vundef; Vundef; Vundef]. cbn [app].
  rewrite upd_Znth0.
  rewrite (upd_Znth_cons 1) by lia. change (1 - 1) with 0. rewrite upd_Znth0.
  rewrite (upd_Znth_cons 2) by lia. change (2 - 1) with 1.
  rewrite (upd_Znth_cons 1) by lia. change (1 - 1) with 0. rewrite upd_Znth0.
  rewrite (upd_Znth_cons 3) by lia. change (3 - 1) with 2.
  rewrite (upd_Znth_cons 2) by lia. change (2 - 1) with 1.
  rewrite (upd_Znth_cons 1) by lia. change (1 - 1) with 0. rewrite upd_Znth0.
  rewrite !upd_Znth_cons by lia.
  replace (4 + Zlength e - 1 - 1 - 1 - 1) with (Zlength (vb e)) by (rewrite Zlength_vb; lia).
  rewrite upd_Znth_char by reflexivity.
  unfold vb. cbn [map]. rewrite map_app. cbn [map app]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma lab_cstr {cs: compspecs} (m: Z) (e: list Z) (p: val):
  0 <= Zlength e <= 16 * m + 1 ->
  data_at Ews (tarray tuchar (16 * m + 6)) (vb (ace e ++ [0]) ++ Zrepeat Vundef (16 * m + 1 - Zlength e)) p
  |-- OpensslPunycode.proof.shim.ShimSpec.cstr Ews (ace e) p * TT.
Proof.
  intros Hb. unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  assert (Ha: Zlength (ace e) = Zlength e + 4) by (unfold ace; rewrite Zlength_app; change (Zlength [120; 110; 45; 45]) with 4; lia).
  rewrite (split2_data_at_Tarray_app (Zlength (ace e) + 1)).
  2: { rewrite Zlength_vb, Zlength_app. reflexivity. }
  2: { rewrite Zlength_Zrepeat by lia. lia. }
  rewrite (data_at_tuchar_cs cs OpensslPunycode.proof.shim.ShimSpec.CS). cancel.
Qed.

(* After u = malloc(ulen); want = malloc(ulen): the NULL tests, at = 0, then stmt_lab_utf8. *)
Definition stmt_lab_test : statement :=
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _u (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                  (Sset _t'15
                                                                    (Econst_int (Int.repr 1) tint))
                                                                  (Sset _t'15
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _want (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                (Sifthenelse (Etempvar _t'15 tint)
                                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                  Sskip))
                                                              (Ssequence
                                                                (Sset _at
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
  stmt_lab_utf8)).

Definition P_lab_test (gv: globals) (cps e: list Z) (pc plab pu pw vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1; one_label_ok cps = true]
  (LOCALx [temp _want pw; temp _u pu; temp _t'22 (Vlong (Int64.repr (Zlength e))); temp _lab plab;
           temp _ulen (Vlong (Int64.repr (ulen_of cps))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (mem_mgr gv ::
         (if eq_dec pw nullval then emp
          else malloc_token Ews (tarray tuchar (ulen_of cps)) pw * data_at_ Ews (tarray tuchar (ulen_of cps)) pw) ::
         (if eq_dec pu nullval then emp
          else malloc_token Ews (tarray tuchar (ulen_of cps)) pu * data_at_ Ews (tarray tuchar (ulen_of cps)) pu) ::
         data_at Ews (tarray tuchar (16 * Zlength cps + 6))
           (vb (ace e ++ [0]) ++ Zrepeat Vundef (16 * Zlength cps + 1 - Zlength e)) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo ::
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv :: OpensslPunycode.proof.punycode.PunySpec.xn_lit gv ::
         OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0 :: TT :: nil))).

Lemma lab_test : piece_utf8_stmt ->
  forall (Espec: OracleKind) gv cps e pc plab pu pw vo ve,
    semax Delta_main (P_lab_test gv cps e pc plab pu pw vo ve) stmt_lab_test (overridePost (Q_ret vo ve) main_ret).
Proof.
  intros HU. intros.
  unfold P_lab_test, stmt_lab_test, main_ret, main_post. abbreviate_semax.
  Intros.
  assert (Hm: 0 <= Zlength cps) by apply Zlength_nonneg.
  assert (He: 0 <= Zlength e) by apply Zlength_nonneg.
  pose proof (ulen_of_bounds cps).
  assert (Hsz: sizeof (tarray tuchar (ulen_of cps)) = ulen_of cps).
  { simpl. rewrite Z.max_r by lia. lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'15 (Vint (Int.repr
      (if eq_dec pu nullval then 1 else if eq_dec pw nullval then 1 else 0))) :: Q) (SEPx R))) end.
  { apply derives_trans with ((if eq_dec pu nullval then emp else malloc_token Ews (tarray tuchar (ulen_of cps)) pu *
      data_at_ Ews (tarray tuchar (ulen_of cps)) pu) * TT)%logic; [cancel | apply malloc_tc_test; rep_lia]. }
  { forward. destruct (eq_dec pu nullval); [ | contradiction]. entailer!. }
  { forward.
    { entailer!. apply derives_trans with ((if eq_dec pw nullval then emp else malloc_token Ews (tarray tuchar (ulen_of cps)) pw *
        data_at_ Ews (tarray tuchar (ulen_of cps)) pw) * TT)%logic; [cancel | apply malloc_tc_test; rep_lia]. }
    destruct (eq_dec pu nullval); [contradiction | ]. destruct (eq_dec pw nullval).
    - subst. entailer!.
    - entailer!. destruct pw; simpl in PNpw; try contradiction; try (subst; exfalso; apply n0; reflexivity); reflexivity. }
  forward_if.
  { clear HU. forward. Exists (Int.repr 0). entailer!. }
  destruct (EqDec_val pu nullval) as [E | Hpu]; [ inversion H5 | ].
  destruct (EqDec_val pw nullval) as [E | Hpw]; [ inversion H5 | ].
  clear H5. rewrite !if_false by assumption. Intros.
  forward.
  eapply semax_pre; [ | apply (HU Espec gv cps e pc plab pu pw vo ve) ].
  unfold P_utf8, main_frame.
  sep_apply (lab_cstr (Zlength cps) e plab); [ lia | ].
  entailer!.
Qed.
