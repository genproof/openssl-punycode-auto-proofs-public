(* ossl_punycode_decode, digit loop: the body (the octet, its digit-value, the overflow test of i), then the
   second half (DecDigB). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecArith.
Require Import OpensslPunycode.proof.punycode.DecDigDefs.
Require Import OpensslPunycode.proof.punycode.DecDigA2.

Lemma zext_sbyte: forall x, 0 <= x <= 255 -> Int.zero_ext 8 (Int.repr (sbyte x)) = Int.repr x.
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  f_equal. rewrite Int.unsigned_repr_eq. change (two_p 8) with 256. change Int.modulus with 4294967296.
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 16777216; lia).
  unfold sbyte. destruct (x <? 128).
  - apply Z.mod_small. lia.
  - replace (x - 256) with (x + (-1) * 256) by lia. rewrite Z_mod_plus by lia. apply Z.mod_small. lia.
Qed.

Lemma dig_body_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos n i bias: Z) (out: list Z) (f: nat) (I J: environ -> mpred) (pos' i' w j: Z),
  readable_share shi -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  0 <= pos < Zlength inp -> 0 <= i -> 0 <= bias <= 2340 ->
  Zlength inp - pos <= Z.of_nat f -> decode inp cap = steps inp f cap pos n i bias out ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
    digits inp (Z.to_nat (Zlength inp - pos')) pos' i' w (36 * (j + 1)) bias ->
  pos <= pos' <= Zlength inp -> i <= i' <= Int.max_unsigned -> 1 <= w <= Int.max_unsigned -> 0 <= j -> 2 ^ j <= w ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _k (Vint (Int.repr (36 * (j + 1)))); temp _w (Vint (Int.repr w));
    temp _oldi (Vint (Int.repr i)); temp _loop (Vint (Int.repr pos')); temp _i (Vint (Int.repr i'));
    temp _n (Vint (Int.repr n)); temp _bias (Vint (Int.repr bias));
    temp _written_out (Vint (Int.repr (Zlength out))); temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
   SEP (data_at Ers tuint (Vint (Int.repr 36)) (gv _base);
   data_at Ers tuint (Vint (Int.repr 1)) (gv _tmin);
   data_at Ers tuint (Vint (Int.repr 26)) (gv _tmax);
   data_at Ers tuint (Vint (Int.repr 38)) (gv _skew);
   data_at Ers tuint (Vint (Int.repr 700)) (gv _damp);
   data_at Ers tuint (Vint (Int.repr 72)) (gv _initial_bias);
   data_at Ers tuint (Vint (Int.repr 128)) (gv _initial_n);
   data_at Ers tuint (Vint (Int.repr (-1))) (gv _maxint);
   data_at Ers tschar (Vint (Int.repr 45)) (gv _delimiter);
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_dig_body
  (dig_R gv shi pe inp sho pd cap init shl pl pos n i bias out I J).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j
  SH H LEN2 POS RI RB FUEL DEC DG H1 H2 H3 H4 H5.
unfold stmt_dig_body, dig_R, dec_post. abbreviate_semax.
  forward_if.
  { match goal with C: Int.unsigned (Int.repr pos') >= _ |- _ => rewrite Int.unsigned_repr in C by rep_lia end.
    assert (DF: decode inp cap = (false, out))
      by (rewrite DEC; apply steps_none; try lia; rewrite DG; apply digits_end; lia).
    forward. rewrite (decode_result_eq inp cap init false out LEN2 DF). cbn [fst snd].
    unfold puny_consts. entailer!. }
  match goal with C: Int.unsigned (Int.repr pos') < _ |- _ => rewrite Int.unsigned_repr in C by rep_lia; rename C into PL end.
  pose proof (bytes_ok_Znth inp pos' H ltac:(lia)) as RX.
  pose proof (sbyte_range _ RX) as RS.
  rewrite arr0_in by (auto; lia).
  forward.
  rewrite <- arr0_in by (auto; lia).
  forward_call (Znth pos' inp).
  { entailer!. simpl. rewrite zext_sbyte by lia. reflexivity. }
  forward. forward.
  rewrite (digits_step inp pos' i' w) in DG by lia. cbv zeta in DG.
  set (x := Znth pos' inp) in *.
  pose proof (digit_value_range x) as DVR.
  destruct (digit_value x =? 36) eqn:DV; [apply Z.eqb_eq in DV | apply Z.eqb_neq in DV].
  { rewrite DV in DG. rewrite (proj2 (Z.leb_le 36 36)) in DG by lia.
    forward_if.
    { assert (DF: decode inp cap = (false, out)) by (rewrite DEC; apply steps_none; try lia; congruence).
      forward. rewrite (decode_result_eq inp cap init false out LEN2 DF). cbn [fst snd].
      unfold puny_consts. entailer!. }
    lia. }
  rewrite (proj2 (Z.leb_gt 36 _)) in DG by lia.
  set (d := digit_value x) in *.
  forward_if. { lia. }
  eapply semax_pre; [ | apply (dig_a2_block Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j d);
    auto; try lia ].
  entailer!.
Qed.
