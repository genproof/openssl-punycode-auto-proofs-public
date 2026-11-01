(* pr_encode, the branch c == n of the pass: the digits of delta, adapt, delta = 0, h++. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDigA.
Require Import OpensslPunycode.proof.harness.EncDigB.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_dig: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Zlength out <= ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_digs
   (overridePost (dig_q shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
     (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros. unfold stmt_digs.
  forward. forward.
  forward_loop (dig_inv shc pc cps sho po ocap oinit shl pl n delta bias h b j out)
    break: (dig_brk shc pc cps sho po ocap oinit shl pl n delta bias h b j out).
  { unfold dig_inv. Exists delta 64%nat (@nil Z). rewrite app_nil_r. entailer!.
    pose proof maxint_lt_pow. lia. }
  { eapply enc_dig_body; eauto. }
  eapply enc_dig_post; eauto.
Qed.
