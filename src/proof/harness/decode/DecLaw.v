(* Law decode: harness_safe of its program from the shared specification library (QuickProof.Assembly). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.proof.harness.decode.DecLawG.
Require OpensslPunycode.proof.harness.decode.DecLawE1.
Require OpensslPunycode.proof.harness.decode.DecLawE2.

Theorem decode_proved : harness_safe p.
Proof.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_app. split.
    + exact OpensslPunycode.proof.harness.decode.DecLawE1.entries_G1.
    + exact OpensslPunycode.proof.harness.decode.DecLawE2.entries_G2.
Qed.
