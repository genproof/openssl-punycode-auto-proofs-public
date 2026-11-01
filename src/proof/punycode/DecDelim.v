(* ossl_punycode_decode: the search of the last delimiter (for (loop = 0; loop < enc_len; loop++) ...). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.

Definition stmt_delim : statement := (Ssequence (Sset _loop (Econst_int (Int.repr 0) tint)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _loop tuint) (Ecast (Etempvar _enc_len tulong) tuint) tint) Sskip Sbreak) (Ssequence (Sset _t'18 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Ssequence (Sset _t'19 (Evar _delimiter tschar)) (Sifthenelse (Ebinop Oeq (Etempvar _t'18 tschar) (Etempvar _t'19 tschar) tint) (Sset _basic_count (Etempvar _loop tuint)) Sskip)))) (Sset _loop (Ebinop Oadd (Etempvar _loop tuint) (Econst_int (Int.repr 1) tint) tuint)))).

Lemma delim_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl (R: ret_assert),
  readable_share shi -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _basic_count (Vint (Int.repr (0)));
    temp _max_out (Vint (Int.repr cap)); temp _written_out (Vint (Int.repr 0));
    temp _processed_in (Vint (Int.repr 0)); temp _bias (Vint (Int.repr 72));
    temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
    temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (data_at Ers tuint (Vint (Int.repr 36)) (gv _base);
   data_at Ers tuint (Vint (Int.repr 1)) (gv _tmin);
   data_at Ers tuint (Vint (Int.repr 26)) (gv _tmax);
   data_at Ers tuint (Vint (Int.repr 38)) (gv _skew);
   data_at Ers tuint (Vint (Int.repr 700)) (gv _damp);
   data_at Ers tuint (Vint (Int.repr 72)) (gv _initial_bias);
   data_at Ers tuint (Vint (Int.repr 128)) (gv _initial_n);
   data_at Ers tuint (Vint (Int.repr (-1))) (gv _maxint);
   data_at Ers tschar (Vint (Int.repr 45)) (gv _delimiter);
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap init pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_delim
  (overridePost (PROP () LOCAL (temp _loop (Vint (Int.repr (Zlength inp))); temp _basic_count (Vint (Int.repr (last_delim inp)));
    temp _max_out (Vint (Int.repr cap)); temp _written_out (Vint (Int.repr 0));
    temp _processed_in (Vint (Int.repr 0)); temp _bias (Vint (Int.repr 72));
    temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
    temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap init pd;
    data_at shl tuint (Vint (Int.repr cap)) pl)) R).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl R SH H LEN2.
destruct R as [Rn Rb Rc Rr]. unfold stmt_delim, overridePost. abbreviate_semax.
set (len := Zlength inp) in *.
assert (LEN: 0 <= len) by apply Zlength_nonneg.
forward_for_simple_bound len (EX j: Z,
  PROP () LOCAL (temp _basic_count (Vint (Int.repr (last_delim (sublist 0 j inp))));
    temp _max_out (Vint (Int.repr cap)); temp _written_out (Vint (Int.repr 0));
    temp _processed_in (Vint (Int.repr 0)); temp _bias (Vint (Int.repr 72));
    temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
    temp _enc_len (Vlong (Int64.repr len)); temp _pDecoded pd; temp _pout_length pl)
  SEP (data_at Ers tuint (Vint (Int.repr 36)) (gv _base);
   data_at Ers tuint (Vint (Int.repr 1)) (gv _tmin);
   data_at Ers tuint (Vint (Int.repr 26)) (gv _tmax);
   data_at Ers tuint (Vint (Int.repr 38)) (gv _skew);
   data_at Ers tuint (Vint (Int.repr 700)) (gv _damp);
   data_at Ers tuint (Vint (Int.repr 72)) (gv _initial_bias);
   data_at Ers tuint (Vint (Int.repr 128)) (gv _initial_n);
   data_at Ers tuint (Vint (Int.repr (-1))) (gv _maxint);
   data_at Ers tschar (Vint (Int.repr 45)) (gv _delimiter);
   arr0 shi tuchar len (vb inp) pe; arr0 sho tuint cap init pd;
   data_at shl tuint (Vint (Int.repr cap)) pl)).
{ rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia; auto. }
{ entailer!. }
{ rewrite arr0_in by (auto; lia).
  pose proof (bytes_ok_Znth inp i H ltac:(lia)) as RX.
  pose proof (sbyte_range _ RX) as RS.
  forward. forward.
  forward_if.
  + match goal with C: sbyte _ = 45 |- _ => rename C into E45 end.
    forward. rewrite <- arr0_in by (auto; lia). entailer!.
    rewrite last_delim_snoc by lia. apply (proj1 (sbyte_eq_45 _ RX)) in E45. rewrite (proj2 (Z.eqb_eq _ _) E45). auto.
  + match goal with C: sbyte _ <> 45 |- _ => rename C into E45 end.
    forward. rewrite <- arr0_in by (auto; lia). entailer!.
    rewrite last_delim_snoc by lia. rewrite (proj2 (Z.eqb_neq _ _)). auto.
    intro. apply E45, (proj2 (sbyte_eq_45 _ RX)); auto. }
rewrite sublist_same by auto.
unfold puny_consts. entailer!.
Qed.
