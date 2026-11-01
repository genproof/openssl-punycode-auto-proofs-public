(* The last piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): ossl_shim_zalloc_failed = 0, the call
   r = ossl_a2ulabel(label, out, outlen), the checks of r, out and want (Ru8Model.ru8_a2ulabel), return 0.
   The proof is Ru8P20Main.piece20_of, applied to the model fact. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.
Require OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P20Main.

Lemma piece20 : piece20_stmt.
Proof. exact (OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P20Main.piece20_of ru8_a2ulabel). Qed.
