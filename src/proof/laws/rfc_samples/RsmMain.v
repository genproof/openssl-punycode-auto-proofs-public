(* The main of harness/rfc_samples.c against main_spec_std (RsmProg: the program, the law's compspecs CS, the
   context Gmain): the globals as process_globals gives them, turned into the predicates of RsmMainDefs
   (RsmGlobA/B/C), then piece 0 (RsmMainLoop). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainGlob.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainLoop.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmGlobA.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmGlobB.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmGlobC.
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

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _count tuint v_count])
    (SEPx [data_at_ Tsh tuint v_count; has_ext tt])) * liftx (globvars2pred gv (varsA ++ varsB ++ varsC)) * emp)%logic).
  { rewrite <- vars_split. go_lowerx. normalize. cancel. }
  simple eapply semax_process_globvars.
  { eapply ENTAIL_trans; [ apply chunkA | ].
    eapply ENTAIL_trans; [ apply chunkB | ].
    apply chunkC. }
  rewrite !sepcon_emp. unfold niceC, niceA. cbn [app].
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (piece0 Espec gv v_count) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts.
    try rewrite !(data_at_tuint_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    try rewrite !(data_at_tschar_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    apply andp_right; [ apply prop_right; rewrite !eqb_type_refl; auto | cancel ]. }
Qed.
