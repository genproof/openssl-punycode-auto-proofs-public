(* The main of harness/api_decode_capacity.c against main_spec_std (DcapProg: the program, the law's
   compspecs CS, the context Gmain). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainDefs.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP0.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP5.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP6.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP7.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP10.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainP15.

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
Proof. exact (piece0 (piece5 (piece6 (piece7 (piece10 piece15))))). Qed.

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  eapply semax_pre with (P' := (PROPx [] (LOCALx (gvars gv :: [lvar _fewer_count tuint v_fewer_count;
    lvar _exact_count tuint v_exact_count; lvar _count tuint v_count])
    (SEPx [data_at_ Tsh tuint v_fewer_count; data_at_ Tsh tuint v_exact_count; data_at_ Tsh tuint v_count;
           has_ext tt])) *
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
  eapply semax_pre; [ | apply (main_chain Espec gv v_count v_exact_count v_fewer_count) ].
  unfold pre0, lvars3. go_lower.
  unfold OpensslPunycode.proof.punycode.PunySpec.puny_consts.
  rewrite delim_tschar.
  apply andp_right; [ apply prop_right; rewrite !eqb_type_refl; auto | cancel ].
Qed.
