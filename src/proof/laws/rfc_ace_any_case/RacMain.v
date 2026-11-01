(* The main of harness/rfc_ace_any_case.c against main_spec_std (RacProg: the program, the law's compspecs CS, the
   context Gmain): the globals of main's precondition in the form the specifications want them, then the pieces
   RacMainP0, P6, P15, P19 (RacMainDefs), chained. *)
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
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainP0.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainP6.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainP15.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainP19.
Local Open Scope logic.

(* Scalars do not depend on the compspecs. *)
Lemma rac_tuint_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma rac_tint_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma rac_tlong_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma rac_tschar_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tschar v p = @data_at cs2 sh tschar v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma rac_tschar5_cs (cs1 cs2: compspecs) sh v p:
  @data_at cs1 sh (tarray tschar 5) v p = @data_at cs2 sh (tarray tschar 5) v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The delimiter '-' is initialized as an octet (Init_int8: VST's tuchar view); punycode.c reads it as char. *)
Lemma rac_delim_tschar sh p:
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
Proof. exact (piece0 (piece6 (piece15 piece19))). Qed.

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx [gvars gv] (SEPx [has_ext tt])) *
    liftx (globvars2pred gv (QPprog_vars p)) * emp)%logic).
  { go_lowerx. normalize. cancel. }
  simple eapply semax_process_globvars.
  { let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x. process_globals. }
  rewrite !sepcon_emp.
  simpl readonly2share.
  rewrite !zero_val_tint. change (Tlong Signed noattr) with tlong. rewrite zero_val_tlong.
  repeat match goal with |- context [mapsto _ _ (gv ?i) _] =>
    assert_PROP (headptr (gv i)) by (apply gvars_denote_HP'; [simpl; auto | reflexivity]);
    erewrite (mapsto_data_at'' _ _ _ _ (gv i)); [ | reflexivity | assumption | apply JMeq_refl] end.
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (main_chain Espec gv) ].
  { unfold pre0. go_lower.
    unfold PS.puny_consts, PS.xn_lit, SS.shim_state.
    try rewrite !(rac_tuint_cs PS.CS CS).
    try rewrite !(rac_tschar_cs PS.CS CS).
    try rewrite !(rac_tschar5_cs PS.CS CS).
    try rewrite !(rac_tint_cs SS.CS CS).
    try rewrite !(rac_tlong_cs SS.CS CS).
    rewrite rac_delim_tschar.
    apply andp_right; [ apply prop_right; auto | cancel ]. }
Qed.
