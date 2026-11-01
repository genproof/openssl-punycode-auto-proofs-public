(* Piece 25 of the main of harness/api_a2ulabel_labels.c: the check that -1 for s1 or for s2 gives -1 for
   s1 '.' s2 (AlbMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Local Open Scope logic.

Lemma piece25 : join_minus1_stmt -> piece26_stmt -> piece25_stmt.
Proof.
  intros Hm H26 Espec gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po.
  unfold pre25, T25, ret0, main_post, Delta_main. abbreviate_semax. Intros.
  pose proof (a2ulabel_res t1 outlen1 ltac:(lia)) as Hr1.
  pose proof (a2ulabel_res t2 outlen2 ltac:(lia)) as Hr2.
  pose proof (Hm t1 t2 outlen1 outlen2 (outlen1 + outlen2) ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
  remember (fst (a2ulabel t1 outlen1)) as r1. remember (fst (a2ulabel t2 outlen2)) as r2.
  remember (fst (a2ulabel (t1 ++ [46] ++ t2) (outlen1 + outlen2))) as r.
  forward_if (temp _t'20 (Vint (Int.repr (if Z.eq_dec r1 (-1) then 1 else if Z.eq_dec r2 (-1) then 1 else 0)))).
  { forward. entailer!.
    destruct Hr1 as [E | [E | E]]; rewrite E in *; try reflexivity;
      match goal with Hx: Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in Hx; [ lia | rep_lia | rep_lia ] end. }
  { forward. entailer!.
    destruct Hr1 as [E | [E | E]]; rewrite E in *;
      [ match goal with Hx: Int.repr _ <> _ |- _ => exfalso; apply Hx; reflexivity end | | ];
      (destruct Hr2 as [E2 | [E2 | E2]]; rewrite E2; reflexivity). }
  forward_if True.
  { assert (r = -1) as ->.
    { apply Hr. destruct (Z.eq_dec r1 (-1)); [ left; auto | ].
      destruct (Z.eq_dec r2 (-1)); [ right; auto | contradiction ]. }
    forward_call. entailer!. }
  { forward. entailer!. }
  Intros.
  subst MORE_COMMANDS POSTCONDITION Delta Delta_specs. unfold abbreviate.
  eapply semax_pre; [ | apply (H26 Espec gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po) ].
  unfold pre25. subst r1 r2 r. entailer!.
Qed.
