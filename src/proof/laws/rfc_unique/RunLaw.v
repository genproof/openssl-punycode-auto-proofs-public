(* Law rfc_unique (harness/rfc_unique.c, with harness/laws_common.h): harness_safe of its program.  The main is
   proved on the specifications of ossl_punycode_decode and of the helpers of laws_common.h (RunLawV.v, whose
   helper bodies are those of src/proof/laws/common/Cmn*.v, so the hypothesis on CommonSpec's bodies is not
   used), from the model fact of RunUniq.v: two inputs decoded into the same code points differ only in the case
   of letters among the deltas. *)
Require Import QuickProof.Contract.
Require OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.contracts.rfc_unique.
Require OpensslPunycode.proof.laws.rfc_unique.RunUniq.
Require OpensslPunycode.proof.laws.rfc_unique.RunLawV.

Lemma rfc_unique_proved :
  OpensslPunycode.proof.laws.common.CommonSpec.common_bodies_stmt ->
  harness_safe OpensslPunycode.contracts.rfc_unique.whole_prog.
Proof.
  intros _.
  exact (OpensslPunycode.proof.laws.rfc_unique.RunLawV.rfc_unique_of_model
           OpensslPunycode.proof.laws.rfc_unique.RunUniq.unique_proved).
Qed.
