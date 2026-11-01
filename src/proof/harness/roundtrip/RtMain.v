(* The main of harness/x_roundtrip.c against main_spec_std (OpensslPunycode.proof.harness.roundtrip.RtProg: the program,
   the law's compspecs CS, the context Gmain).
   The start of main is proved here (the globals, m, cps); the rest is the chain of pieces Main*.v (MainDefs.v). *)
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs OpensslPunycode.proof.harness.roundtrip.RtMainLib.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainGlob OpensslPunycode.proof.harness.roundtrip.RtMainStart.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainModel.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainFinal.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainUtf8.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLab.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainIf.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainMallocs.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainEcap.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLoop1.

Lemma body_main_of :
  decode_encode_stmt -> encode_chars_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
intros DE EC.
pose proof (piece_loop1 (piece_ecap (piece_mallocs DE EC (piece_if (piece_lab EC
  (piece_utf8 (piece_final DE EC (a2u_model DE EC)))))))) as L1.
start_function.
eapply semax_seq with (Q := FF); [ | apply semax_ff ].
eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _olen tuint v_olen; lvar _elen tulong v_elen]) (SEPx [data_at_ Tsh tuint v_olen; data_at_ Tsh tulong v_elen; has_ext tt])) * liftx (globvars2pred gv (QPprog_vars p)) * emp)%logic).
{ go_lowerx. normalize. cancel. }
simple eapply semax_process_globvars.
{ let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x. process_globals. }
rewrite !sepcon_emp.
repeat change_mapsto_gvar_to_data_at.
simpl readonly2share.
eapply semax_pre; [ | apply (piece_start L1 Espec gv v_olen v_elen) ].
unfold P_start, main_frame.
go_lowerx. sep_apply (main_globals gv). eapply derives_trans; [ apply (add_mem_mgr gv) | ]. entailer!.
Qed.
