(* The body of ossl_punycode_decode (crypto/punycode.c, patched: I2), under Punycode.CS. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecDelim.
Require Import OpensslPunycode.proof.punycode.DecBasic.
Require Import OpensslPunycode.proof.punycode.DecLoop.

Lemma body_decode_main : semax_body Vprog Gprog_decode f_ossl_punycode_decode ossl_punycode_decode_spec.
Proof.
start_function.
unfold puny_consts. Intros.
forward. forward. forward. forward. forward. forward. forward.
set (len := Zlength inp) in *.
assert (LEN: 0 <= len) by apply Zlength_nonneg.
forward_if.
{ forward.
  rewrite Int.unsigned_repr in H3 by rep_lia.
  unfold decode_result. rewrite (proj2 (Z.leb_le _ _)) by (fold len; rep_lia). simpl.
  unfold puny_consts. entailer!. }
rewrite (eq_refl: Int.unsigned (Int.add (Int.mul (Int.repr 2147483647) (Int.repr 2)) (Int.repr 1)) = Int.max_unsigned) in H3.
assert (LEN2: len < Int.max_unsigned) by (clear - H3; rep_lia). clear H3.
unfold MORE_COMMANDS, abbreviate.
unfold len in *. clear len.
eapply semax_seq.
{ apply (delim_block Espec gv shi pe inp sho pd cap init shl pl); auto. }
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ apply (basic_block Espec gv shi pe inp sho pd cap init shl pl); auto. }
Intros.
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ apply (loop_block Espec gv shi pe inp sho pd cap init shl pl); auto. }
Intros out.
assert (DT: decode inp cap = (true, out)) by auto.
forward. forward.
rewrite (decode_result_eq _ _ _ true out LEN2 DT). cbn [fst snd].
entailer!.
Qed.
