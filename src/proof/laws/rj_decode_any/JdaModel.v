(* What the law rj_decode_any checks of ossl_punycode_decode's result, as a fact about PunySpec.decode_result: the
   result is 0 or 1; on 1 the length is at most the capacity, on 0 it is the capacity (plain Coq). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.ARDecRange.

Lemma jda_result bs c init:
  bytes_ok bs -> 0 <= c ->
  let res := OpensslPunycode.proof.punycode.PunySpec.decode_result bs c init in
  (fst (fst res) = 0 /\ snd res = c) \/ (fst (fst res) = 1 /\ 0 <= snd res <= c).
Proof.
  intros OK Hc. unfold OpensslPunycode.proof.punycode.PunySpec.decode_result.
  destruct (Int.max_unsigned <=? Zlength bs); [ left; auto | ].
  pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range bs c OK Hc) as [_ Hl].
  destruct (decode bs c) as [ok out]. simpl in Hl.
  destruct ok; simpl; [ right; split; [ auto | split; [ apply Zlength_nonneg | exact Hl ] ] | left; auto ].
Qed.
