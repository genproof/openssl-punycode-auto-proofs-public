(* Law a2ulabel: harness_safe of its program from the shared specification library (QuickProof.Assembly). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uLawG.
Require OpensslPunycode.proof.harness.a2ulabel.A2uLawE1 OpensslPunycode.proof.harness.a2ulabel.A2uLawE2.

Theorem a2ulabel_proved : harness_safe p.
Proof.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.harness.a2ulabel.A2uLawE1.entries_G1.
    + exact OpensslPunycode.proof.harness.a2ulabel.A2uLawE2.entries_G2.
Qed.
