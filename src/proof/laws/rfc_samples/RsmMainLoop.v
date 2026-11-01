(* Piece 0 of the main of harness/rfc_samples.c: at = 0, the loop over the 19 samples (each iteration is
   RsmMainA.iter_piece) and return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainA.
Local Open Scope logic.

Opaque pts dec enc lit_ids start expected.

Lemma piece0 : piece0_stmt.
Proof.
  intros Espec gv vc. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward.
  forward_for_simple_bound 19 (EX s: Z, inv gv vc s).
  { unfold inv. entailer!. }
  { unfold inv. Intros.
    eapply semax_Delta_subsumption; [ | apply (iter_piece Espec gv vc i H) ].
    unfold Delta, abbreviate, Delta_main. apply tycontext_sub_refl. }
  forward. Exists (Int.repr 0). entailer!.
Qed.
