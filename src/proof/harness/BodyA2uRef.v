(* The bodies of pr_put and pr_a2ulabel (harness/puny_ref.h), under the a2ulabel harness's compspecs.
  *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require OpensslPunycode.proof.harness.BodyPrPut.
Require OpensslPunycode.proof.harness.ARMain.

Lemma a2uref_bodies :
  semax_body Vprog Gprog_put f_pr_put pr_put_spec /\
  semax_body Vprog Gprog_a2ulabel f_pr_a2ulabel pr_a2ulabel_spec.
Proof.
  split.
  - exact OpensslPunycode.proof.harness.BodyPrPut.body_pr_put_proof.
  - exact OpensslPunycode.proof.harness.ARMain.body_pr_a2ulabel_main.
Qed.

Definition body_pr_put : semax_body Vprog Gprog_put f_pr_put pr_put_spec := proj1 a2uref_bodies.
Definition body_pr_a2ulabel : semax_body Vprog Gprog_a2ulabel f_pr_a2ulabel pr_a2ulabel_spec :=
  proj2 a2uref_bodies.
