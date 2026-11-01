(* Shared vocabulary of the proof of ossl_punycode_decode (split over several files): the main-loop invariant,
   the function's postcondition as a ret_assert, small facts about octets read as char. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.

Lemma sbyte_range: forall b, 0 <= b <= 255 -> -128 <= sbyte b <= 127.
Proof. intros. unfold sbyte. destruct (b <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. Qed.

Lemma sbyte_small: forall b, 0 <= b < 128 -> sbyte b = b.
Proof. intros. unfold sbyte. rewrite (proj2 (Z.ltb_lt _ _)) by lia. auto. Qed.

Lemma arr0_in {cs: compspecs}: forall sh len inp p, bytes_ok inp -> len <> 0 ->
  arr0 sh tuchar len (vb inp) p = data_at sh (tarray tschar len) (map (fun b => Vint (Int.repr (sbyte b))) inp) p.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_tschar; auto. Qed.

Lemma sbyte_eq_45: forall b, 0 <= b <= 255 -> (sbyte b = 45 <-> b = 45).
Proof. intros. unfold sbyte. destruct (b <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. Qed.

Lemma bytes_ok_Znth: forall l j, bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l <= 255.
Proof. intros. unfold bytes_ok in H. rewrite Forall_Znth in H. specialize (H j H0). simpl in H. rep_lia. Qed.

Lemma is_basic_sbyte: forall x, 0 <= x <= 255 -> (Int.unsigned (Int.repr (sbyte x)) <? 128) = (x <? 128).
Proof.
  intros. unfold sbyte. destruct (x <? 128) eqn:E.
  - rewrite Int.unsigned_repr by rep_lia. auto.
  - apply Z.ltb_ge in E. rewrite Int.unsigned_repr_eq. change Int.modulus with 4294967296.
    replace (x - 256) with ((x - 256 + 4294967296) + (-1) * 4294967296) by lia.
    rewrite Z_mod_plus by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

(* The statements of ossl_punycode_decode proved by separate lemmas (copied from its Clight body). *)
Definition stmt_basic : statement := (Sifthenelse (Ebinop Ogt (Etempvar _basic_count tuint) (Econst_int (Int.repr 0) tint) tint) (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _basic_count tuint) (Etempvar _max_out tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _loop (Econst_int (Int.repr 0) tint)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _loop tuint) (Etempvar _basic_count tuint) tint) Sskip Sbreak) (Ssequence (Ssequence (Ssequence (Sset _t'17 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Scall (Some _t'1) (Evar _is_basic (Tfunction (tuint :: nil) tint cc_default)) ((Etempvar _t'17 tschar) :: nil))) (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint) (Econst_int (Int.repr 0) tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Ssequence (Sset _t'16 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _loop tuint) (tptr tuint)) tuint) (Etempvar _t'16 tschar))) (Sset _written_out (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint))))) (Sset _loop (Ebinop Oadd (Etempvar _loop tuint) (Econst_int (Int.repr 1) tint) tuint)))) (Sset _processed_in (Ebinop Oadd (Etempvar _basic_count tuint) (Econst_int (Int.repr 1) tint) tuint)))) Sskip).

Definition stmt_digits : statement := (Ssequence (Sset _k (Evar _base tuint)) (Sloop (Ssequence Sskip (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _loop tuint) (Etempvar _enc_len tulong) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Ssequence (Sset _t'15 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Scall (Some _t'2) (Evar _digit_decoded  (Tfunction (tuchar :: nil) tint cc_default)) ((Etempvar _t'15 tschar) :: nil))) (Sset _digit (Etempvar _t'2 tint))) (Ssequence (Sset _loop (Ebinop Oadd (Etempvar _loop tuint) (Econst_int (Int.repr 1) tint) tuint)) (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _digit tint) (Econst_int (Int.repr 0) tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _t'14 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ecast (Etempvar _digit tint) tuint) (Ebinop Odiv (Ebinop Osub (Etempvar _t'14 tuint) (Etempvar _i tuint) tuint) (Etempvar _w tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Ebinop Omul (Etempvar _digit tint) (Etempvar _w tuint) tuint) tuint)) (Ssequence (Ssequence (Sifthenelse (Ebinop Ole (Etempvar _k tuint) (Etempvar _bias tuint) tint) (Ssequence (Sset _t'13 (Evar _tmin tuint)) (Sset _t'3 (Ecast (Etempvar _t'13 tuint) tuint))) (Ssequence (Sset _t'11 (Evar _tmax tuint)) (Sifthenelse  (Ebinop Oge (Etempvar _k tuint) (Ebinop Oadd (Etempvar _bias tuint) (Etempvar _t'11 tuint) tuint) tint) (Ssequence (Ssequence (Sset _t'12 (Evar _tmax tuint)) (Sset _t'3 (Ecast (Etempvar _t'12 tuint) tuint))) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint))) (Ssequence (Sset _t'3 (Ecast (Ebinop Osub (Etempvar _k tuint) (Etempvar _bias tuint) tuint) tuint)) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint)))))) (Sset _t (Etempvar _t'3 tuint))) (Ssequence (Sifthenelse (Ebinop Olt (Ecast (Etempvar _digit tint) tuint) (Etempvar _t tuint) tint) Sbreak Sskip) (Ssequence (Ssequence (Sset _t'9 (Evar _maxint tuint)) (Ssequence (Sset _t'10 (Evar _base tuint)) (Sifthenelse  (Ebinop Ogt (Etempvar _w tuint) (Ebinop Odiv (Etempvar _t'9 tuint) (Ebinop Osub (Etempvar _t'10 tuint) (Etempvar _t tuint) tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))) (Ssequence (Sset _t'8 (Evar _base tuint)) (Sset _w (Ebinop Omul (Etempvar _w tuint) (Ebinop Osub (Etempvar _t'8 tuint) (Etempvar _t tuint) tuint) tuint))))))))))))) (Ssequence (Sset _t'7 (Evar _base tuint)) (Sset _k (Ebinop Oadd (Etempvar _k tuint) (Etempvar _t'7 tuint) tuint))))).

Definition stmt_rest : statement := (Ssequence (Ssequence (Scall (Some _t'4) (Evar _adapt (Tfunction (tuint :: tuint :: tuint :: nil) tint cc_default)) ((Ebinop Osub (Etempvar _i tuint) (Etempvar _oldi tuint) tuint) :: (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) :: (Ebinop Oeq (Etempvar _oldi tuint) (Econst_int (Int.repr 0) tint) tint) :: nil)) (Sset _bias (Etempvar _t'4 tint))) (Ssequence (Ssequence (Sset _t'6 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ebinop Odiv (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) (Ebinop Osub (Etempvar _t'6 tuint) (Etempvar _n tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _n (Ebinop Oadd (Etempvar _n tuint) (Ebinop Odiv (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) tuint)) (Ssequence (Sset _i (Ebinop Omod (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint)) (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _written_out tuint) (Etempvar _max_out tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _gp_j (Etempvar _written_out tuint)) (Sloop (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _gp_j tuint) (Etempvar _i tuint) tint) Sskip Sbreak) (Ssequence (Sset _t'5 (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint) (tptr tuint)) tuint)) (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _gp_j tuint) (tptr tuint)) tuint) (Etempvar _t'5 tuint)))) (Sset _gp_j (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint)))) (Ssequence (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _i tuint) (tptr tuint)) tuint) (Etempvar _n tuint)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)) (Sset _written_out (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint)))))))))).

Definition stmt_insert : statement := (Ssequence (Sset _gp_j (Etempvar _written_out tuint)) (Sloop (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _gp_j tuint) (Etempvar _i tuint) tint) Sskip Sbreak) (Ssequence (Sset _t'5 (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint) (tptr tuint)) tuint)) (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _gp_j tuint) (tptr tuint)) tuint) (Etempvar _t'5 tuint)))) (Sset _gp_j (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint)))).

Section Inv.
Variables (gv: globals) (shi: share) (pe: val) (inp: list Z) (sho: share) (pd: val) (cap: Z) (init: list val)
  (shl: share) (pl: val).

(* The ret_assert of the body of ossl_punycode_decode (after start_function). *)
Definition dec_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP ( )
        RETURN (Vint (Int.repr (fst (fst (decode_result inp cap init)))))
        SEP (puny_consts gv; arr0 shi tuchar (Zlength inp) (vb inp) pe;
             arr0 sho tuint cap (snd (fst (decode_result inp cap init))) pd;
             data_at shl tuint (Vint (Int.repr (snd (decode_result inp cap init)))) pl)))
    (stackframe_of f_ossl_punycode_decode).

(* The invariant of the main loop: the model state (pos, n, i, bias, out) with fuel f. *)
Definition dec_inv : environ -> mpred :=
  EX pos: Z, EX n: Z, EX i: Z, EX bias: Z, EX out: list Z, EX f: nat,
  PROP (0 <= Zlength out <= pos; pos <= Zlength inp; Zlength out <= cap; 0 <= i <= Zlength out;
        128 <= n <= Int.max_unsigned; 0 <= bias <= 2340; Zlength inp - pos <= Z.of_nat f;
        decode inp cap = steps inp f cap pos n i bias out)
  LOCAL (temp _loop (Vint (Int.repr pos)); temp _n (Vint (Int.repr n)); temp _i (Vint (Int.repr i));
         temp _bias (Vint (Int.repr bias)); temp _written_out (Vint (Int.repr (Zlength out)));
         temp _max_out (Vint (Int.repr cap)); gvars gv; temp _pEncoded pe;
         temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
  SEP (puny_consts gv;
   arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
   data_at shl tuint (Vint (Int.repr cap)) pl).

End Inv.
