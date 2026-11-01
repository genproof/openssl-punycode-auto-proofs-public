(* ossl_punycode_decode: the digit loop of one delta (for (k = base;; k += base) {...}); its body in DecDigA. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecDigDefs.
Require Import OpensslPunycode.proof.punycode.DecDigA.

Lemma digits_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos n i bias: Z) (out: list Z) (f: nat) (I J: environ -> mpred),
  readable_share shi -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  0 <= pos < Zlength inp -> 0 <= i <= Int.max_unsigned -> 0 <= bias <= 2340 ->
  Zlength inp - pos <= Z.of_nat f -> decode inp cap = steps inp f cap pos n i bias out ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _w (Vint (Int.repr 1)); temp _oldi (Vint (Int.repr i)); temp _loop (Vint (Int.repr pos));
    temp _n (Vint (Int.repr n)); temp _i (Vint (Int.repr i)); temp _bias (Vint (Int.repr bias));
    temp _written_out (Vint (Int.repr (Zlength out))); temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
   SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_digits
  (overridePost (dig_brk gv shi pe inp sho pd cap init shl pl pos n i bias out)
   (loop1_ret_assert I (overridePost J (dec_post gv shi pe inp sho pd cap init shl pl)))).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J SH H LEN2 POS RI RB FUEL DEC.
unfold stmt_digits. abbreviate_semax.
unfold puny_consts. Intros.
forward.
forward_loop (dig_inv gv shi pe inp sho pd cap init shl pl pos n i bias out)
  continue: (dig_cont gv shi pe inp sho pd cap init shl pl pos n i bias out)
  break: (dig_brk gv shi pe inp sho pd cap init shl pl pos n i bias out).
{ unfold dig_inv. Exists pos i 1 0. entailer!. }
{ unfold dig_inv. Intros pos' i' w j.
  apply (dig_body_block Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j); auto; lia. }
{ unfold dig_cont. Intros pos' i' w j. forward. forward. unfold dig_inv. Exists pos' i' w (j + 1).
  replace (36 * (j + 2)) with (36 * (j + 1 + 1)) in * by lia.
  entailer!. do 2 f_equal. lia. }
apply andp_left2. apply derives_refl.
Qed.
