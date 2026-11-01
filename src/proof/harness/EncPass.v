(* pr_encode: one iteration of the pass over the code points for code point n. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncPassLt.
Require Import OpensslPunycode.proof.harness.EncPassGe.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_pass_body: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (f: nat) (n h0 B j: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  0 <= j < Zlength cps -> 0 <= h0 <= Zlength cps -> 0 <= B <= Int.max_unsigned -> 0 <= n <= maxint ->
  semax DeltaE (pass_st shc pc cps sho po ocap oinit shl pl f n h0 B j j) stmt_passbody
    (overridePost (pass_st shc pc cps sho po ocap oinit shl pl f n h0 B (j + 1) j)
      (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros. unfold pass_st, stmt_passbody, enc_post. abbreviate_semax.
  Intros delta bias h out. rename H10 into Hk, H11 into Hh, H12 into Hd, H13 into Hb, H14 into Ho.
  pose proof (Zlength_nonneg out) as Hol.
  pose proof (cnt_eq_nonneg n (sublist 0 j cps)) as Hcn0.
  assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H2; apply H2; apply Znth_In; lia).
  assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
  rewrite (sublist_next j (Zlength cps) cps) in Hk by lia.
  pose proof (cnt_eq_succ n cps j H6) as Hcnt.
  pose proof (cnt_eq_le n (sublist 0 j cps)) as Hcl. rewrite Zlength_sublist in Hcl by lia.
  set (c := Znth j cps) in *.
  rewrite (arr0_ne shc tuint) by lia.
  forward.
  { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  forward.
  rewrite <- (arr0_ne shc tuint) by lia.
  rewrite Int.unsigned_repr by rep_lia.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  destruct (Z.lt_ge_cases c n) as [Hlt|Hge].
  - eapply enc_pass_lt; eauto.
  - eapply enc_pass_ge; eauto.
Qed.
