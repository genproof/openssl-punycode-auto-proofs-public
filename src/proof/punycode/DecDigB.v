(* ossl_punycode_decode, digit loop: the second half of the body (the threshold, the break, the w update). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecArith.
Require Import OpensslPunycode.proof.punycode.DecDigDefs.

Lemma dig_b_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos n i bias: Z) (out: list Z) (f: nat) (I J: environ -> mpred) (pos' i' w j d: Z),
  bytes_ok inp -> Zlength inp < Int.max_unsigned -> 0 <= pos < Zlength inp -> 0 <= bias <= 2340 ->
  Zlength inp - pos <= Z.of_nat f -> decode inp cap = steps inp f cap pos n i bias out ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
   (if d <? threshold (36 * (j + 1)) bias then Some (i' + d * w, pos' + 1)
    else if maxint <? w * (36 - threshold (36 * (j + 1)) bias) then None
    else digits inp (Z.to_nat (Zlength inp - (pos' + 1))) (pos' + 1) (i' + d * w)
           (w * (36 - threshold (36 * (j + 1)) bias)) (36 * (j + 1) + 36) bias) ->
  pos <= pos' < Zlength inp -> i <= i' -> i' + d * w <= maxint -> 1 <= w <= Int.max_unsigned ->
  0 <= j < 32 -> 2 ^ j <= w -> 0 <= d <= 35 ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _i (Vint (Int.repr (i' + d * w))); temp _loop (Vint (Int.repr (pos' + 1)));
    temp _digit (Vint (Int.repr d)); temp _k (Vint (Int.repr (36 * (j + 1)))); temp _w (Vint (Int.repr w));
    temp _oldi (Vint (Int.repr i));
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
  stmt_dig_b
  (dig_R gv shi pe inp sho pd cap init shl pl pos n i bias out I J).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j d
  H LEN2 POS RB FUEL DEC DG H1 H2 NOV H3 J32 H5 H0.
unfold stmt_dig_b, dig_R, dec_post. abbreviate_semax.
  pose proof (threshold_range (36 * (j + 1)) bias) as TR.
  forward_if (PROP ()
    LOCAL (temp _t'3 (Vint (Int.repr (threshold (36 * (j + 1)) bias))); temp _i (Vint (Int.repr (i' + d * w)));
     temp _loop (Vint (Int.repr (pos' + 1))); temp _digit (Vint (Int.repr d));
     temp _k (Vint (Int.repr (36 * (j + 1)))); temp _w (Vint (Int.repr w)); temp _oldi (Vint (Int.repr i));
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
    data_at shl tuint (Vint (Int.repr cap)) pl)).
  { forward. forward. entailer!. unfold threshold. rewrite (proj2 (Z.leb_le _ _)) by rep_lia. auto. }
  { forward. forward_if.
    - forward. forward. forward. entailer!. unfold threshold.
      rewrite (proj2 (Z.leb_gt _ _)) by rep_lia. rewrite (proj2 (Z.leb_le _ _)) by rep_lia. auto.
    - forward. forward. entailer!. unfold threshold.
      rewrite (proj2 (Z.leb_gt _ _)) by rep_lia. rewrite (proj2 (Z.leb_gt (bias + 26) _)) by rep_lia. auto. }
  forward.
  set (t := threshold (36 * (j + 1)) bias) in *.
  forward_if.
  { try rewrite Int.unsigned_repr in * by rep_lia.
    rewrite (proj2 (Z.ltb_lt d t)) in DG by lia.
    forward. unfold dig_brk. Exists (i' + d * w) (pos' + 1). unfold puny_consts. entailer!. unfold maxint in *. assert (0 <= d * w) by (apply Z.mul_nonneg_nonneg; lia). rep_lia. }
  try rewrite Int.unsigned_repr in * by rep_lia.
  rewrite (proj2 (Z.ltb_ge d t)) in DG by lia.
  forward. forward.
  forward_if.
  { entailer!. match goal with C: Int.repr _ = Int.zero |- _ => revert C end. apply repr_nonzero; rep_lia. }
  { match goal with C: Int.unsigned (Int.divu _ _) < _ |- _ => rewrite divu_m1 in C by rep_lia;
      apply test_w in C; try lia; rename C into OV end.
    rewrite (proj2 (Z.ltb_lt _ _) OV) in DG.
    assert (DF: decode inp cap = (false, out)) by (rewrite DEC; apply steps_none; try lia; auto).
    forward. rewrite (decode_result_eq inp cap init false out LEN2 DF). cbn [fst snd].
    unfold puny_consts. entailer!. }
  match goal with C: Int.unsigned (Int.divu _ _) >= _ |- _ => rewrite divu_m1 in C by rep_lia; rename C into NOW0 end.
  assert (NOW: w * (36 - t) <= maxint).
  { destruct (Z_le_gt_dec (w * (36 - t)) maxint); auto.
    pose proof (proj2 (test_w w (36 - t) ltac:(lia) ltac:(lia)) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_ge _ _) NOW) in DG.
  forward. forward.
  unfold dig_cont. Exists (pos' + 1) (i' + d * w) (w * (36 - t)) j.
  replace (36 * (j + 1) + 36) with (36 * (j + 2)) in DG by lia.
  entailer!.
  unfold maxint in *. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
  assert (0 <= d * w) by (apply Z.mul_nonneg_nonneg; lia).
  assert (w * 10 <= w * (36 - t)) by (apply Z.mul_le_mono_nonneg_l; lia).
  repeat split; try rep_lia. Qed.
