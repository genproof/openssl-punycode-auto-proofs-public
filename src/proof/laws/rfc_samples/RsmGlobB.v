(* The globals of harness/rfc_samples.c, chunk B (RsmMainGlob.varsB): the 19 string literals of the samples, as
   process_globals gives them, turned into RsmMainDefs.lits. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.punycode.code.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainGlob.
Local Open Scope logic.

Module PC := OpensslPunycode.punycode.code.

(* The headptr of a global of the program. *)
Ltac glob_hp H := eapply gvars_denote_HP; [ eassumption | exact H | reflexivity ].

(* The literal of sample s, from the form process_globals gives it. *)
Ltac conv_lit gv s :=
  let id := eval vm_compute in (Znth s lit_ids) in
  match goal with |- context [data_at ?sh ?t ?l (gv id)] =>
    rewrite (lit_conv gv s sh t l (gv id) ltac:(lia) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; apply JMeq_refl) ltac:(vm_compute; reflexivity))
  end.

Lemma chunkB gv R rest :
  ENTAIL Delta_main, globvars_in_process gv R emp (varsB ++ rest) |-- globvars_in_process gv (lits gv :: R) emp rest.
Proof.
  unfold Delta_main. simplify_func_tycontext.
  unfold varsB. cbn [app].
  do 19 process_idstar.
  apply gip_derives. intros rho Htc Hgv.
  simpl fold_right_sepcon.
  conv_lit gv 0.
  conv_lit gv 1.
  conv_lit gv 2.
  conv_lit gv 3.
  conv_lit gv 4.
  conv_lit gv 5.
  conv_lit gv 6.
  conv_lit gv 7.
  conv_lit gv 8.
  conv_lit gv 9.
  conv_lit gv 10.
  conv_lit gv 11.
  conv_lit gv 12.
  conv_lit gv 13.
  conv_lit gv 14.
  conv_lit gv 15.
  conv_lit gv 16.
  conv_lit gv 17.
  conv_lit gv 18.
  sep_apply (lits19 gv).
  fold fold_right_sepcon. cancel.
Qed.
