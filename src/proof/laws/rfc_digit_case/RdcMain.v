(* The main of harness/rfc_digit_case.c against main_spec_std (RdcProg: the program, the law's compspecs CS, the
   context Gmain). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainP0.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainP6.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainP7.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainP9.
Local Open Scope logic.

Lemma data_at_tuint_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma data_at_tschar_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tschar v p = @data_at cs2 sh tschar v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The delimiter '-' is initialized as an octet (Init_int8: VST's tuchar view); punycode.c reads it as char. *)
Lemma delim_tschar sh p:
  data_at sh tuchar (Vint (Int.zero_ext 8 (Int.repr 45))) p = data_at sh tschar (Vint (Int.repr 45)) p.
Proof.
  rewrite <- (data_at_singleton_array_eq sh tuchar _ [Vint (Int.zero_ext 8 (Int.repr 45))] p eq_refl).
  rewrite <- (data_at_singleton_array_eq sh tschar _ [Vint (Int.repr 45)] p eq_refl).
  change [Vint (Int.zero_ext 8 (Int.repr 45))] with (map Vubyte [Byte.repr 45]).
  change [Vint (Int.repr 45)] with (map Vbyte [Byte.repr 45]).
  symmetry. apply data_at_tarray_tschar_tuchar.
Qed.

(* The pieces, chained: from the start of the body to its end. *)
Lemma main_chain: piece0_stmt.
Proof. exact (piece0 (piece6 (piece7 piece9))). Qed.

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _count1 tuint v_count1; lvar _count2 tuint v_count2])
    (SEPx [data_at_ Tsh tuint v_count1; data_at_ Tsh tuint v_count2; has_ext tt])) *
    liftx (globvars2pred gv (QPprog_vars p)) * emp)%logic).
  { go_lowerx. normalize. cancel. }
  simple eapply semax_process_globvars.
  { let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x. process_globals. }
  rewrite !sepcon_emp.
  simpl readonly2share.
  repeat match goal with |- context [mapsto _ _ (gv ?i) _] =>
    assert_PROP (headptr (gv i)) by (apply gvars_denote_HP'; [simpl; auto | reflexivity]);
    erewrite (mapsto_data_at'' _ _ _ _ (gv i)); [ | reflexivity | assumption | apply JMeq_refl] end.
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (main_chain Espec gv v_count1 v_count2) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts.
    try rewrite !(data_at_tuint_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(data_at_tschar_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    rewrite delim_tschar.
    apply andp_right; [ apply prop_right; rewrite !eqb_type_refl; auto | cancel ]. }
Qed.
