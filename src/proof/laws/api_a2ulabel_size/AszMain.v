(* The main of harness/api_a2ulabel_size.c against main_spec_std (AszProg: the program, the law's compspecs CS, the
   context Gmain).  Here: the globals of main's precondition in the form the specifications want them (as in the
   main of x_a2ulabel, whose lemmas on globals are reused); the body in the pieces AszMainP0, AszMainP9,
   AszMainP12, AszMainP15. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.a2ulabel.A2uMain.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainDefs.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainP0.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainP9.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainP12.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainP15.

Module AM := OpensslPunycode.proof.harness.a2ulabel.A2uMain.

(* globvars2pred in main's precondition, in the form VST's semax_process_globvars expects (main has no local
   variable, so the globals come first in SEP). *)
Lemma move_globvars0 {cs: compspecs} {Espec: OracleKind} Delta gv l R2 c Post:
  semax Delta (PROPx [] (LOCALx [gvars gv] (SEPx R2)) *
               (@liftx (LiftEnviron mpred) (globvars2pred gv l)) * emp)%logic c Post ->
  semax Delta (PROPx [] (LOCALx [gvars gv] (SEPx (globvars2pred gv l :: R2)))) c Post.
Proof.
  intros H. eapply semax_pre; [ | exact H ].
  intro rho. unfold PROPx, LOCALx, SEPx, local, lift1. unfold_lift. simpl.
  rewrite !sepcon_emp. normalize. cancel.
Qed.

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

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  match goal with |- context [globvars2pred gv (QPprog_vars p)] =>
    let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x end.
  apply move_globvars0.
  simple eapply semax_process_globvars; [process_globals | apply finish_process_globvars].
  simpl readonly2share.
  rewrite !zero_val_tint. change (Tlong Signed noattr) with tlong. rewrite zero_val_tlong.
  rewrite sepcon_emp.
  repeat match goal with |- context [mapsto _ _ (gv ?i) _] =>
    assert_PROP (headptr (gv i)) by (apply gvars_denote_HP'; [simpl; auto | reflexivity]);
    erewrite (mapsto_data_at'' _ _ _ _ (gv i)); [ | reflexivity | assumption | apply JMeq_refl] end.
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (piece0 (piece9 (piece12 piece15)) Espec gv) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts, OpensslPunycode.proof.punycode.PunySpec.xn_lit,
      OpensslPunycode.proof.shim.ShimSpec.shim_state.
    try rewrite !(AM.data_at_tuint_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tschar_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tschar5_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(AM.data_at_tint_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    try rewrite !(AM.data_at_tlong_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite <- delim_tschar_cs.
    apply andp_right; [ apply prop_right; auto | cancel ]. }
Qed.
