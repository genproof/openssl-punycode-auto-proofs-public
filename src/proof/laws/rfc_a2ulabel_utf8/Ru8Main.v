(* The main of harness/rfc_a2ulabel_utf8.c against main_spec_std (Ru8Prog: the program, the law's compspecs CS, the
   context Gmain): the globals of main's precondition in the form the specifications want them (as in the main of
   x_a2ulabel, whose lemmas on globals are reused), then the body in the pieces of Ru8MainDefs, chained. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.a2ulabel.A2uMain.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP0.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP7.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP13.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP14.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP17.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainP20.

Module AM := OpensslPunycode.proof.harness.a2ulabel.A2uMain.

(* The delimiter '-' is initialized as an octet (Init_int8: VST's tuchar view); punycode.c reads it as char. *)
Lemma delim_tschar_cs {cs: compspecs} sh q:
  @data_at cs sh tuchar (Vint (Int.zero_ext 8 (Int.repr 45))) q = @data_at cs sh tschar (Vint (Int.repr 45)) q.
Proof.
  rewrite <- (data_at_singleton_array_eq sh tuchar _ [Vint (Int.zero_ext 8 (Int.repr 45))] q eq_refl).
  rewrite <- (data_at_singleton_array_eq sh tschar _ [Vint (Int.repr 45)] q eq_refl).
  change [Vint (Int.zero_ext 8 (Int.repr 45))] with (map Vubyte [Byte.repr 45]).
  change [Vint (Int.repr 45)] with (map Vbyte [Byte.repr 45]).
  symmetry. apply data_at_tarray_tschar_tuchar.
Qed.

(* The pieces, chained: from the start of the body to its end. *)
Lemma main_chain: piece0_stmt.
Proof. exact (piece0 (piece7 (piece13 (piece14 (piece17 piece20))))). Qed.

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _count tuint v_count])
    (SEPx [data_at_ Tsh tuint v_count; has_ext tt])) *
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
  eapply semax_pre; [ | apply (main_chain Espec gv v_count) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts, OpensslPunycode.proof.punycode.PunySpec.xn_lit,
      OpensslPunycode.proof.shim.ShimSpec.shim_state.
    try rewrite !(AM.data_at_tuint_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tschar_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tschar5_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tint_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    try rewrite !(AM.data_at_tlong_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite <- delim_tschar_cs.
    apply andp_right; [ apply prop_right; rewrite ?eqb_type_refl; auto | cancel ]. }
Qed.
