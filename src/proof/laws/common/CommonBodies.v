(* The bodies of the helpers of harness/laws_common.h against their specifications (HelperSpec.v), one per file
   (Cmn*.v), gathered as common_bodies_stmt. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.laws.common.CommonSpec.
Require OpensslPunycode.proof.laws.common.CmnUpto.
Require OpensslPunycode.proof.laws.common.CmnAnyBytes.
Require OpensslPunycode.proof.laws.common.CmnAnyUints.
Require OpensslPunycode.proof.laws.common.CmnCopyOf.
Require OpensslPunycode.proof.laws.common.CmnBytesEq.
Require OpensslPunycode.proof.laws.common.CmnUintsEq.
Require OpensslPunycode.proof.laws.common.CmnLastDelim.

Lemma common_bodies : common_bodies_stmt.
Proof.
  exact (conj OpensslPunycode.proof.laws.common.CmnUpto.body_upto
        (conj OpensslPunycode.proof.laws.common.CmnAnyBytes.body_any_bytes
        (conj OpensslPunycode.proof.laws.common.CmnAnyUints.body_any_uints
        (conj OpensslPunycode.proof.laws.common.CmnCopyOf.body_copy_of
        (conj OpensslPunycode.proof.laws.common.CmnBytesEq.body_bytes_eq
        (conj OpensslPunycode.proof.laws.common.CmnUintsEq.body_uints_eq
              OpensslPunycode.proof.laws.common.CmnLastDelim.body_last_delimiter)))))).
Qed.
