(* pr_encode, the branch c == n of the pass: one iteration of the digit loop, from the digit written. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDigA3.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_dig_body2: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z) Q (q: Z) (f3: nat) (wr: list Z) (k t: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Zlength out <= ocap ->
  k = 36 + 36 * (64 - Z.of_nat (S f3)) -> t = threshold k bias ->
  enc_digits 64 delta 36 bias = wr ++ enc_digits (S f3) q k bias ->
  0 <= q < 10 ^ Z.of_nat (S f3) -> q <= maxint -> (S f3 <= 64)%nat -> t <= q ->
  Zlength (out ++ wr) < ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _t (Vlong (Int64.repr t)); temp _q (Vlong (Int64.repr q)); temp _k (Vlong (Int64.repr k));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength (out ++ wr))));
      temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv (out ++ wr) ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_digbody2
   (loop_nocontinue_ret_assert (dig_inv shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
     (overridePost (dig_brk shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
       (overridePost Q (enc_post shc pc cps sho po ocap oinit shl pl)))).
Proof.
  intros until t. intros ? ? ? ? ? ? H5 ? ? ? ? ? Hk Ht Hd Hq Hqm Hf Htq Hw.
  unfold dig_inv, dig_brk, stmt_digbody2, enc_post.
  abbreviate_semax.
  pose proof (Zlength_nonneg (out ++ wr)) as Hwl.
  subst k t. set (k := 36 + 36 * (64 - Z.of_nat (S f3))) in *.
  pose proof (threshold_range k bias) as Htr. set (t := threshold k bias) in *.
  assert (Hm: 0 <= (q - t) mod (36 - t) < 36 - t) by (apply Z.mod_pos_bound; lia).
  forward_call (t + (q - t) mod (36 - t)).
  all: try repr0_false.
  all: try (entailer!; rewrite ?sub64_repr; rewrite modu_repr64 by (unfold maxint in *; rep_lia);
            rewrite add64_repr; auto).
  rewrite (arr0_ne sho tuchar ocap) by lia.
  forward.
  pose proof (digit_char_range (t + (q - t) mod (36 - t)) ltac:(lia)) as Hdc.
  rewrite zext8 by lia. rewrite bufv_upd by lia. rewrite <- (arr0_ne sho tuchar ocap) by lia.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply (enc_dig_body3 shc pc cps sho po ocap oinit shl pl n delta bias h b j out f rest q f3 wr k t);
    auto; try reflexivity.
Qed.
