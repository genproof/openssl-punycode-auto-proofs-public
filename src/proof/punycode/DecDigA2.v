(* ossl_punycode_decode, digit loop: the overflow test of i + digit * w and the update of i, then the second
   half of the body (DecDigB). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecArith.
Require Import OpensslPunycode.proof.punycode.DecDigDefs.
Require Import OpensslPunycode.proof.punycode.DecDigB.

Definition stmt_dig_a2 : statement := (Ssequence (Ssequence (Sset _t'14 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ecast (Etempvar _digit tint) tuint) (Ebinop Odiv (Ebinop Osub (Etempvar _t'14 tuint) (Etempvar _i tuint) tuint) (Etempvar _w tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Ebinop Omul (Etempvar _digit tint) (Etempvar _w tuint) tuint) tuint)) stmt_dig_b)).

Lemma dig_a2_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos n i bias: Z) (out: list Z) (f: nat) (I J: environ -> mpred) (pos' i' w j d: Z),
  bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  0 <= pos < Zlength inp -> 0 <= i -> 0 <= bias <= 2340 ->
  Zlength inp - pos <= Z.of_nat f -> decode inp cap = steps inp f cap pos n i bias out ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
   (if maxint <? i' + d * w then None
    else if d <? threshold (36 * (j + 1)) bias then Some (i' + d * w, pos' + 1)
    else if maxint <? w * (36 - threshold (36 * (j + 1)) bias) then None
    else digits inp (Z.to_nat (Zlength inp - (pos' + 1))) (pos' + 1) (i' + d * w)
           (w * (36 - threshold (36 * (j + 1)) bias)) (36 * (j + 1) + 36) bias) ->
  pos <= pos' < Zlength inp -> i <= i' <= Int.max_unsigned -> 1 <= w <= Int.max_unsigned -> 0 <= j -> 2 ^ j <= w ->
  0 <= d <= 35 ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _loop (Vint (Int.repr (pos' + 1))); temp _digit (Vint (Int.repr d));
    temp _k (Vint (Int.repr (36 * (j + 1)))); temp _w (Vint (Int.repr w));
    temp _oldi (Vint (Int.repr i)); temp _i (Vint (Int.repr i'));
    temp _n (Vint (Int.repr n)); temp _bias (Vint (Int.repr bias));
    temp _written_out (Vint (Int.repr (Zlength out))); temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (data_at Ers tuint (Vint (Int.repr 36)) (gv _base);
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
  stmt_dig_a2
  (dig_R gv shi pe inp sho pd cap init shl pl pos n i bias out I J).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j d
  H LEN2 POS RI RB FUEL DEC DG H1 H2 H3 H4 H5 DR.
unfold stmt_dig_a2, dig_R, dec_post. abbreviate_semax.
forward.
  assert (J32: j < 32).
  { destruct (Z_lt_le_dec j 32); auto. assert (2 ^ 32 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia). rep_lia. }
  forward_if.
  { entailer!. match goal with C: Int.repr _ = Int.zero |- _ => revert C end. apply repr_nonzero; rep_lia. }
  { match goal with C: Int.unsigned (Int.divu _ _) < _ |- _ => rewrite divu_m1_sub in C by rep_lia;
      apply test_digit in C; try (unfold maxint; rep_lia); try lia; rename C into OV end.
    rewrite (proj2 (Z.ltb_lt _ _) OV) in DG.
    assert (DF: decode inp cap = (false, out)) by (rewrite DEC; apply steps_none; try lia; auto).
    forward. rewrite (decode_result_eq inp cap init false out LEN2 DF). cbn [fst snd].
    unfold puny_consts. entailer!. }
  match goal with C: Int.unsigned (Int.divu _ _) >= _ |- _ => rewrite divu_m1_sub in C by rep_lia; rename C into NOV0 end.
  assert (NOV: i' + d * w <= maxint).
  { destruct (Z_le_gt_dec (i' + d * w) maxint); auto. pose proof (proj2 (test_digit i' d w ltac:(unfold maxint; rep_lia) ltac:(lia) ltac:(lia)) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_ge _ _) NOV) in DG.
  forward.
  eapply semax_pre; [ | apply (dig_b_block Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f I J pos' i' w j d);
    auto; try lia ].
  entailer!.
Qed.
