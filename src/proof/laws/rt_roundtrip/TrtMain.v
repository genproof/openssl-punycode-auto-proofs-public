(* The main of harness/rt_roundtrip.c against main_spec_std, given the round trip of the model. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainP0.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainP5.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainP6.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainP8.
Local Open Scope logic.

(* The delimiter '-' is initialized as an octet (Init_int8: VST's tuchar view); punycode.c reads it as char. *)
Lemma trt_delim_tschar sh p:
  data_at sh tuchar (Vint (Int.zero_ext 8 (Int.repr 45))) p = data_at sh tschar (Vint (Int.repr 45)) p.
Proof.
  rewrite <- (data_at_singleton_array_eq sh tuchar _ [Vint (Int.zero_ext 8 (Int.repr 45))] p eq_refl).
  rewrite <- (data_at_singleton_array_eq sh tschar _ [Vint (Int.repr 45)] p eq_refl).
  change [Vint (Int.zero_ext 8 (Int.repr 45))] with (map Vubyte [Byte.repr 45]).
  change [Vint (Int.repr 45)] with (map Vbyte [Byte.repr 45]).
  symmetry. apply data_at_tarray_tschar_tuchar.
Qed.

(* The pieces, chained: from the start of the body to its end, given the round trip of the model. *)
Lemma main_chain: trt_model_stmt -> piece0_stmt.
Proof. intros HM. exact (piece0 (piece5 (piece6 (piece8 HM)))). Qed.

Lemma body_main : trt_model_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  intros HM.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _len tulong v_len; lvar _count tuint v_count])
    (SEPx [data_at_ Tsh tulong v_len; data_at_ Tsh tuint v_count; has_ext tt]))
    * liftx (globvars2pred gv (QPprog_vars p)) * emp)%logic).
  { go_lowerx. normalize. cancel. }
  simple eapply semax_process_globvars.
  { let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x. process_globals. }
  rewrite !sepcon_emp.
  simpl readonly2share.
  repeat match goal with |- context [mapsto _ _ (gv ?i) _] =>
    assert_PROP (headptr (gv i)) by (apply gvars_denote_HP'; [simpl; auto | reflexivity]);
    erewrite (mapsto_data_at'' _ _ _ _ (gv i)); [ | reflexivity | assumption | apply JMeq_refl] end.
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (main_chain HM Espec gv v_len v_count) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts.
    (* the constants are stated at the unit's compspecs, convertible with the law's *)
    change (@data_at OpensslPunycode.proof.punycode.PunySpec.CS) with (@data_at CS).
    rewrite trt_delim_tschar.
    apply andp_right; [ apply prop_right; rewrite !eqb_type_refl; auto | cancel ]. }
Qed.
