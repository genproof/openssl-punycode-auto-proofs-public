(* Definitions shared by the files of the digit loop of ossl_punycode_decode. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.

(* The statements of the digit loop of ossl_punycode_decode (copied from its Clight body): the loop body (after
   its leading skip) and its second half (from the threshold on). *)
Definition stmt_dig_b : statement := (Ssequence (Ssequence (Sifthenelse (Ebinop Ole (Etempvar _k tuint) (Etempvar _bias tuint) tint) (Ssequence (Sset _t'13 (Evar _tmin tuint)) (Sset _t'3 (Ecast (Etempvar _t'13 tuint) tuint))) (Ssequence (Sset _t'11 (Evar _tmax tuint)) (Sifthenelse  (Ebinop Oge (Etempvar _k tuint) (Ebinop Oadd (Etempvar _bias tuint) (Etempvar _t'11 tuint) tuint) tint) (Ssequence (Ssequence (Sset _t'12 (Evar _tmax tuint)) (Sset _t'3 (Ecast (Etempvar _t'12 tuint) tuint))) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint))) (Ssequence (Sset _t'3 (Ecast (Ebinop Osub (Etempvar _k tuint) (Etempvar _bias tuint) tuint) tuint)) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint)))))) (Sset _t (Etempvar _t'3 tuint))) (Ssequence (Sifthenelse (Ebinop Olt (Ecast (Etempvar _digit tint) tuint) (Etempvar _t tuint) tint) Sbreak Sskip) (Ssequence (Ssequence (Sset _t'9 (Evar _maxint tuint)) (Ssequence (Sset _t'10 (Evar _base tuint)) (Sifthenelse  (Ebinop Ogt (Etempvar _w tuint) (Ebinop Odiv (Etempvar _t'9 tuint) (Ebinop Osub (Etempvar _t'10 tuint) (Etempvar _t tuint) tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))) (Ssequence (Sset _t'8 (Evar _base tuint)) (Sset _w (Ebinop Omul (Etempvar _w tuint) (Ebinop Osub (Etempvar _t'8 tuint) (Etempvar _t tuint) tuint) tuint)))))).

Definition stmt_dig_body : statement := (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _loop tuint) (Etempvar _enc_len tulong) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Ssequence (Sset _t'15 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Scall (Some _t'2) (Evar _digit_decoded  (Tfunction (tuchar :: nil) tint cc_default)) ((Etempvar _t'15 tschar) :: nil))) (Sset _digit (Etempvar _t'2 tint))) (Ssequence (Sset _loop (Ebinop Oadd (Etempvar _loop tuint) (Econst_int (Int.repr 1) tint) tuint)) (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _digit tint) (Econst_int (Int.repr 0) tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _t'14 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ecast (Etempvar _digit tint) tuint) (Ebinop Odiv (Ebinop Osub (Etempvar _t'14 tuint) (Etempvar _i tuint) tuint) (Etempvar _w tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Ebinop Omul (Etempvar _digit tint) (Etempvar _w tuint) tuint) tuint)) stmt_dig_b)))))).

Section Dig.
Variables (gv: globals) (shi: share) (pe: val) (inp: list Z) (sho: share) (pd: val) (cap: Z) (init: list val)
  (shl: share) (pl: val) (pos n i bias: Z) (out: list Z).

(* The invariant of the digit loop (k = 36 (j + 1)), at its continue point, and its exit. *)
Definition dig_inv : environ -> mpred :=
  EX pos': Z, EX i': Z, EX w: Z, EX j: Z,
  PROP (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
          digits inp (Z.to_nat (Zlength inp - pos')) pos' i' w (36 * (j + 1)) bias;
        pos <= pos' <= Zlength inp; i <= i' <= Int.max_unsigned; 1 <= w <= Int.max_unsigned; 0 <= j; 2 ^ j <= w)
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
    data_at shl tuint (Vint (Int.repr cap)) pl).

Definition dig_cont : environ -> mpred :=
  EX pos': Z, EX i': Z, EX w: Z, EX j: Z,
  PROP (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
          digits inp (Z.to_nat (Zlength inp - pos')) pos' i' w (36 * (j + 2)) bias;
        pos <= pos' <= Zlength inp; i <= i' <= Int.max_unsigned; 1 <= w <= Int.max_unsigned; 0 <= j; 2 ^ (j + 1) <= w)
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
    data_at shl tuint (Vint (Int.repr cap)) pl).

Definition dig_brk : environ -> mpred :=
  EX i1: Z, EX pos1: Z,
  PROP (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1);
        i <= i1 <= Int.max_unsigned; pos < pos1 <= Zlength inp)
  LOCAL (temp _oldi (Vint (Int.repr i)); temp _loop (Vint (Int.repr pos1)); temp _i (Vint (Int.repr i1));
    temp _n (Vint (Int.repr n)); temp _bias (Vint (Int.repr bias));
    temp _written_out (Vint (Int.repr (Zlength out))); temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
  SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl).

(* The ret_assert of the body of the digit loop. *)
Definition dig_R (I J: environ -> mpred) : ret_assert :=
  loop1_ret_assert dig_cont
    (overridePost dig_brk (overridePost dig_brk
      (loop1_ret_assert I (overridePost J (dec_post gv shi pe inp sho pd cap init shl pl))))).

End Dig.
