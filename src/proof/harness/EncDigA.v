(* pr_encode, the branch c == n of the pass: one iteration of the digit loop. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDigA2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_dig_body: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z) Q,
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Zlength out <= ocap ->
  semax DeltaE (dig_inv shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
   (Ssequence stmt_digbody1 Sskip)
   (loop_nocontinue_ret_assert (dig_inv shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
     (overridePost (dig_brk shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
       (overridePost Q (enc_post shc pc cps sho po ocap oinit shl pl)))).
Proof.
  intros. unfold dig_inv, dig_brk, stmt_digbody1, enc_post.
  abbreviate_semax.
  Intros q f2 wr. rename H11 into Hd, H12 into Hq, H13 into Hqm, H14 into Hf, H15 into Hw.
  pose proof (Zlength_nonneg (out ++ wr)) as Hwl.
  forward_call (36 + 36 * (64 - Z.of_nat f2), bias).
  set (k := 36 + 36 * (64 - Z.of_nat f2)) in *.
  pose proof (threshold_range k bias) as Ht.
  set (t := threshold k bias) in *.
  forward_if.
  { fix_ltu. forward. Exists q wr. entailer!. rewrite (enc_digits_last f2 q k bias) in Hd; [auto | assumption | lia]. }
  forward_if.
  { forward. apply ret0_entail; [ | apply bufv_len; lia].
    eapply (kont_dig_fail cps f n rest _ _ _ b out wr (enc_digits f2 q k bias)).
    rewrite H5, Hd. reflexivity. apply enc_digits_nonempty. lia. }
  fix_ltu. destruct f2 as [|f3]; [simpl in Hq; lia|].
  try unfold MORE_COMMANDS; unfold abbreviate in *.
  eapply enc_dig_body2; eauto; reflexivity.
Qed.
