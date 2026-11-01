(* The main of harness/x_a2ulabel.c against main_spec_std (OpensslPunycode.proof.harness.a2ulabel.A2uProg: the program,
   the law's compspecs CS, the context Gmain).  Here: the globals of main's precondition in the form the
   specifications want them; the body in the pieces MainP0 .. MainP21 (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP0.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP5.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP6.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP10.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP11.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP15.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP16.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP20.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP20e.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainP21.

(* globvars2pred in main's precondition, in the form VST's semax_process_globvars expects. *)
Lemma move_globvars {cs: compspecs} {Espec: OracleKind} Delta gv l L R1 R2 c Post:
  semax Delta (PROPx [] (LOCALx (gvars gv :: L) (SEPx (R1 :: R2))) *
               (@liftx (LiftEnviron mpred) (globvars2pred gv l)) * emp)%logic c Post ->
  semax Delta (PROPx [] (LOCALx (L ++ [gvars gv]) (SEPx (R1 :: globvars2pred gv l :: R2)))) c Post.
Proof.
  intros H. eapply semax_pre; [ | exact H ].
  intro rho. unfold PROPx, LOCALx, SEPx, local, lift1. unfold_lift. simpl.
  rewrite !sepcon_emp. normalize.
  apply andp_right.
  - apply prop_right. clear - H1. revert H1. induction L; simpl; [ tauto | ].
    intros [A B]. specialize (IHL B). tauto.
  - cancel.
Qed.

(* Scalars do not depend on the compspecs. *)
Lemma data_at_tuint_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma data_at_tint_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma data_at_tlong_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma data_at_tschar_cs1 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tschar v p = @data_at cs2 sh tschar v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.
Lemma data_at_tschar5_cs1 (cs1 cs2: compspecs) sh v p:
  @data_at cs1 sh (tarray tschar 5) v p = @data_at cs2 sh (tarray tschar 5) v p.
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
Lemma main_chain {Espec: OracleKind} gv v_k:
  semax Delta_main (pre0 gv v_k) (Ssequence T0 ret0) main_post.
Proof.
  apply piece0. intros n pin psnap pcps Hn. apply piece5; [ | exact Hn ].
  apply piece6. intros bs. apply piece10. intros sl. apply piece11.
  - intros outlen m. apply piece15.
  - intros outlen m out want ob. apply piece16. intros fn mf. apply piece20.
    + apply piece20e.
    + intros l fn' zf. apply piece21.
Qed.

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  match goal with |- context [globvars2pred gv (QPprog_vars p)] =>
    let x := eval vm_compute in (QPprog_vars p) in change (QPprog_vars p) with x end.
  apply (move_globvars _ gv _ [_]).
  simple eapply semax_process_globvars; [process_globals | apply finish_process_globvars].
  simpl readonly2share.
  rewrite !zero_val_tint. change (Tlong Signed noattr) with tlong. rewrite zero_val_tlong.
  rewrite sepcon_emp.
  repeat match goal with |- context [mapsto _ _ (gv ?i) _] =>
    assert_PROP (headptr (gv i)) by (apply gvars_denote_HP'; [simpl; auto | reflexivity]);
    erewrite (mapsto_data_at'' _ _ _ _ (gv i)); [ | reflexivity | assumption | apply JMeq_refl] end.
  sep_apply (create_mem_mgr gv).
  eapply semax_pre; [ | apply (main_chain gv v_k) ].
  { unfold pre0. go_lower.
    unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts, OpensslPunycode.proof.punycode.PunySpec.xn_lit,
      OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(data_at_tuint_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    rewrite !(data_at_tschar_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    rewrite !(data_at_tschar5_cs1 OpensslPunycode.proof.punycode.PunySpec.CS CS).
    rewrite !(data_at_tint_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite !(data_at_tlong_cs1 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite delim_tschar.
    apply andp_right; [ apply prop_right; unfold t_sink; rewrite eqb_type_refl; auto | cancel ]. }
Qed.
