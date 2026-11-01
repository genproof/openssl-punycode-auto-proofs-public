(* pr_encode, the branch c == n of the pass: after the digit loop (the last digit, adapt, delta = 0, h++). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDigB2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_dig_post: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Zlength out <= ocap ->
  semax DeltaE (dig_brk shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
   stmt_digpost
   (overridePost (dig_q shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
     (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros. unfold dig_brk, dig_q, stmt_digpost, enc_post.
  abbreviate_semax.
  Intros q wr. rename H11 into Hd, H12 into Hq, H13 into Hw.
  pose proof (Zlength_nonneg (out ++ wr)) as Hwl.
  forward_if.
  { forward. apply ret0_entail; [ | apply bufv_len; lia].
    eapply (kont_dig_fail cps f n rest _ _ _ b out wr [digit_char q]).
    rewrite H5, Hd. reflexivity. rewrite Zlength_cons, Zlength_nil. lia. lia. }
  forward_call q.
  pose proof (digit_char_range q ltac:(lia)) as Hdc.
  rewrite (arr0_ne sho tuchar ocap) by lia.
  forward.
  rewrite zext8 by lia. rewrite bufv_upd by lia. rewrite <- (arr0_ne sho tuchar ocap) by lia.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply (enc_dig_post2 shc pc cps sho po ocap oinit shl pl n delta bias h b j out f rest q wr); auto.
Qed.
