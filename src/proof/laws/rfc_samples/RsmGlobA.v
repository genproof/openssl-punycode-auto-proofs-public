(* The globals of harness/rfc_samples.c, chunk A (RsmMainGlob.varsA): the shim's state, four constants of
   punycode.c, encoded[] and two blocks of the code under test, as process_globals gives them, turned into
   encoded_at and the data_at of the constants (the rest is dropped into TT). *)
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

Definition niceA (gv: globals) : list mpred :=
  [encoded_at gv; data_at Ers tuint (Vint (Int.repr 38)) (gv PC._skew);
   data_at Ers tuint (Vint (Int.repr 72)) (gv PC._initial_bias);
   data_at Ers tuint (Vint (Int.repr 128)) (gv PC._initial_n);
   data_at Ers tuint (Vint (Int.repr (-1))) (gv PC._maxint); TT].

(* The headptr of a global of the program. *)
Ltac glob_hp H := eapply gvars_denote_HP; [ eassumption | exact H | reflexivity ].

(* Cell s of encoded[], from the form process_globals gives it. *)
Ltac conv_cell gv Htc HE s :=
  let id := eval vm_compute in (Znth s lit_ids) in
  let off := eval vm_compute in (8 * s)%Z in
  let H := fresh "HP" in
  assert (H: isptr (gv (Znth s lit_ids)))
    by (replace (Znth s lit_ids) with id by (vm_compute; reflexivity);
        let H' := fresh in assert (H': headptr (gv id)) by glob_hp Htc; destruct H' as [? ->]; exact I);
  match goal with |- context [mapsto Ers ?t (offset_val off ?a) ?v] =>
    rewrite (cell_conv gv s t (offset_val off a) v HE H ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity))
  end;
  clear H.

Ltac conv_cell0 gv Htc HE :=
  let id := eval vm_compute in (Znth 0 lit_ids) in
  let H := fresh "HP" in
  assert (H: isptr (gv (Znth 0 lit_ids)))
    by (replace (Znth 0 lit_ids) with id by (vm_compute; reflexivity);
        let H' := fresh in assert (H': headptr (gv id)) by glob_hp Htc; destruct H' as [? ->]; exact I);
  match goal with |- context [mapsto Ers (Tpointer ?x ?y) (gv ?e) ?v] =>
    rewrite (cell_conv0 gv (Tpointer x y) (gv e) v HE H ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
  end;
  clear H.

(* A constant c of punycode.c at the global i. *)
Ltac conv_tuint gv Htc i c :=
  let e := eval vm_compute in i in
  match goal with |- context [mapsto ?sh ?t (gv e) ?v] =>
    rewrite (tuint_conv gv i sh t (gv e) v c ltac:(glob_hp Htc) ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity) ltac:(reflexivity))
  end.

Lemma chunkA gv R rest :
  ENTAIL Delta_main, globvars_in_process gv R emp (varsA ++ rest) |-- globvars_in_process gv (niceA gv ++ R) emp rest.
Proof.
  unfold Delta_main. simplify_func_tycontext.
  unfold varsA. cbn [app].
  do 10 process_idstar.
  apply gip_derives. intros rho Htc Hgv.
  assert (HE: headptr (gv _encoded)) by glob_hp Htc.
  unfold niceA. cbn [app]. simpl fold_right_sepcon.
  conv_cell0 gv Htc HE.
  conv_cell gv Htc HE 1. conv_cell gv Htc HE 2. conv_cell gv Htc HE 3. conv_cell gv Htc HE 4.
  conv_cell gv Htc HE 5. conv_cell gv Htc HE 6. conv_cell gv Htc HE 7. conv_cell gv Htc HE 8.
  conv_cell gv Htc HE 9. conv_cell gv Htc HE 10. conv_cell gv Htc HE 11. conv_cell gv Htc HE 12.
  conv_cell gv Htc HE 13. conv_cell gv Htc HE 14. conv_cell gv Htc HE 15. conv_cell gv Htc HE 16.
  conv_cell gv Htc HE 17. conv_cell gv Htc HE 18.
  sep_apply (cells19 gv HE).
  conv_tuint gv Htc PC._skew 38. conv_tuint gv Htc PC._initial_bias 72.
  conv_tuint gv Htc PC._initial_n 128. conv_tuint gv Htc PC._maxint (-1).
  fold fold_right_sepcon. cancel.
Qed.
