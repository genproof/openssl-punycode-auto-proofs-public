(* The globals of harness/rfc_samples.c, chunk C (RsmMainGlob.varsC): points[], decoded[] and five constants of
   punycode.c, as process_globals gives them, turned into points_at, decoded_at and the data_at of the
   constants. *)
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

Definition niceC (gv: globals) : list mpred :=
  [points_at gv; decoded_at gv; data_at Ers tuint (Vint (Int.repr 700)) (gv PC._damp);
   data_at Ers tschar (Vint (Int.repr 45)) (gv PC._delimiter);
   data_at Ers tuint (Vint (Int.repr 1)) (gv PC._tmin); data_at Ers tuint (Vint (Int.repr 26)) (gv PC._tmax);
   data_at Ers tuint (Vint (Int.repr 36)) (gv PC._base)].

(* A constant c of punycode.c at the global i. *)
Ltac conv_tuint gv Htc i c :=
  let e := eval vm_compute in i in
  match goal with |- context [mapsto ?sh ?t (gv e) ?v] =>
    rewrite (tuint_conv gv i sh t (gv e) v c ltac:(glob_hp Htc) ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity) ltac:(reflexivity))
  end.

Lemma chunkC gv R :
  ENTAIL Delta_main, globvars_in_process gv R emp varsC |-- globvars_in_process gv (niceC gv ++ R) emp [].
Proof.
  unfold Delta_main. simplify_func_tycontext.
  unfold varsC.
  repeat process_idstar.
  apply gip_derives. intros rho Htc Hgv.
  unfold niceC. cbn [app]. simpl fold_right_sepcon.
  let e := eval vm_compute in _points in
  match goal with |- context [data_at ?sh ?t ?l (gv e)] =>
    rewrite (points_conv gv sh t l (gv e) ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; apply JMeq_refl)
      ltac:(reflexivity))
  end.
  let e := eval vm_compute in _decoded in
  match goal with |- context [data_at ?sh ?t ?l (gv e)] =>
    rewrite (decoded_conv gv sh t l (gv e) ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; apply JMeq_refl)
      ltac:(reflexivity))
  end.
  conv_tuint gv Htc PC._damp 700. conv_tuint gv Htc PC._tmin 1. conv_tuint gv Htc PC._tmax 26.
  conv_tuint gv Htc PC._base 36.
  let e := eval vm_compute in PC._delimiter in
  match goal with |- context [mapsto ?sh ?t (gv e) ?v] =>
    rewrite (delim_conv gv PC._delimiter sh t (gv e) v ltac:(glob_hp Htc) ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity) ltac:(reflexivity))
  end.
  fold fold_right_sepcon. cancel.
Qed.
