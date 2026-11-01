(* ======================================================================
   The 19 laws, one theorem each, with the names and the statements that
   quickproof/tools/new_contract.py generated in src/contracts/<law>.v
   (`Theorem <law> : harness_safe whole_prog`, there with that file's
   whole_prog; see the commit tagged `contract`).  They are stated here
   because the proof Requires those files for whole_prog: proving them in
   place would be a cycle, so the contract files keep only their generated
   program.  Each is a projection of a proved conjunction of suite.v: the
   3 x_ laws of `suite_x`, which proves them on one shared model and one
   specification per function of the code under test, and the 16 short
   laws of `suite`, the generated conjunction of all 19 laws.
   ====================================================================== *)

Require Import QuickProof.Contract.
Require OpensslPunycode.contracts.api_a2ulabel_copy.
Require OpensslPunycode.contracts.api_a2ulabel_labels.
Require OpensslPunycode.contracts.api_a2ulabel_nul.
Require OpensslPunycode.contracts.api_a2ulabel_size.
Require OpensslPunycode.contracts.api_decode_capacity.
Require OpensslPunycode.contracts.api_decode_deterministic.
Require OpensslPunycode.contracts.rfc_a2ulabel_utf8.
Require OpensslPunycode.contracts.rfc_ace_any_case.
Require OpensslPunycode.contracts.rfc_basic_first.
Require OpensslPunycode.contracts.rfc_digit_case.
Require OpensslPunycode.contracts.rfc_samples.
Require OpensslPunycode.contracts.rfc_unique.
Require OpensslPunycode.contracts.rj_a2ulabel_any.
Require OpensslPunycode.contracts.rj_decode_any.
Require OpensslPunycode.contracts.rj_decode_invalid.
Require OpensslPunycode.contracts.rt_roundtrip.
Require OpensslPunycode.contracts.x_a2ulabel.
Require OpensslPunycode.contracts.x_decode.
Require OpensslPunycode.contracts.x_roundtrip.
Require OpensslPunycode.contracts.suite.

(* The 3 x_ laws: projections of `suite_x`. *)

Theorem x_a2ulabel : harness_safe OpensslPunycode.contracts.x_a2ulabel.whole_prog.
Proof. exact (proj1 OpensslPunycode.contracts.suite.suite_x). Qed.

Theorem x_decode : harness_safe OpensslPunycode.contracts.x_decode.whole_prog.
Proof. exact (proj1 (proj2 OpensslPunycode.contracts.suite.suite_x)). Qed.

Theorem x_roundtrip : harness_safe OpensslPunycode.contracts.x_roundtrip.whole_prog.
Proof. exact (proj2 (proj2 OpensslPunycode.contracts.suite.suite_x)). Qed.

(* The 16 short laws: projections of `suite` (its conjuncts in order; the last one is `suite_x`). *)

Theorem api_a2ulabel_copy : harness_safe OpensslPunycode.contracts.api_a2ulabel_copy.whole_prog.
Proof. exact (proj1 OpensslPunycode.contracts.suite.suite). Qed.

Theorem api_a2ulabel_labels : harness_safe OpensslPunycode.contracts.api_a2ulabel_labels.whole_prog.
Proof. exact (proj1 (proj2 OpensslPunycode.contracts.suite.suite)). Qed.

Theorem api_a2ulabel_nul : harness_safe OpensslPunycode.contracts.api_a2ulabel_nul.whole_prog.
Proof. exact (proj1 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))). Qed.

Theorem api_a2ulabel_size : harness_safe OpensslPunycode.contracts.api_a2ulabel_size.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))). Qed.

Theorem api_decode_capacity : harness_safe OpensslPunycode.contracts.api_decode_capacity.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))). Qed.

Theorem api_decode_deterministic : harness_safe OpensslPunycode.contracts.api_decode_deterministic.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))). Qed.

Theorem rfc_a2ulabel_utf8 : harness_safe OpensslPunycode.contracts.rfc_a2ulabel_utf8.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))))). Qed.

Theorem rfc_ace_any_case : harness_safe OpensslPunycode.contracts.rfc_ace_any_case.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))))). Qed.

Theorem rfc_basic_first : harness_safe OpensslPunycode.contracts.rfc_basic_first.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))))))). Qed.

Theorem rfc_digit_case : harness_safe OpensslPunycode.contracts.rfc_digit_case.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))))))). Qed.

Theorem rfc_samples : harness_safe OpensslPunycode.contracts.rfc_samples.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))))))))). Qed.

Theorem rfc_unique : harness_safe OpensslPunycode.contracts.rfc_unique.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))))))))). Qed.

Theorem rj_a2ulabel_any : harness_safe OpensslPunycode.contracts.rj_a2ulabel_any.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))))))))))). Qed.

Theorem rj_decode_any : harness_safe OpensslPunycode.contracts.rj_decode_any.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))))))))))). Qed.

Theorem rj_decode_invalid : harness_safe OpensslPunycode.contracts.rj_decode_invalid.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite))))))))))))))). Qed.

Theorem rt_roundtrip : harness_safe OpensslPunycode.contracts.rt_roundtrip.whole_prog.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 OpensslPunycode.contracts.suite.suite)))))))))))))))). Qed.
