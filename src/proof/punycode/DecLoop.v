(* ossl_punycode_decode: the main loop (one delta per iteration: DecDigits, then DecRest). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecDigDefs.
Require Import OpensslPunycode.proof.punycode.DecDigits.
Require Import OpensslPunycode.proof.punycode.DecRest.

Definition stmt_mainloop : statement := (Ssequence (Sset _loop (Etempvar _processed_in tuint)) (Swhile (Ebinop Olt (Etempvar _loop tuint) (Ecast (Etempvar _enc_len tulong) tuint) tint) (Ssequence (Sset _oldi (Etempvar _i tuint)) (Ssequence (Sset _w (Econst_int (Int.repr 1) tint)) (Ssequence (Ssequence (Sset _k (Evar _base tuint)) (Sloop (Ssequence Sskip (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _loop tuint) (Etempvar _enc_len tulong) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Ssequence (Sset _t'15 (Ederef (Ebinop Oadd (Etempvar _pEncoded (tptr tschar)) (Etempvar _loop tuint) (tptr tschar)) tschar)) (Scall (Some _t'2) (Evar _digit_decoded  (Tfunction (tuchar :: nil) tint cc_default)) ((Etempvar _t'15 tschar) :: nil))) (Sset _digit (Etempvar _t'2 tint))) (Ssequence (Sset _loop (Ebinop Oadd (Etempvar _loop tuint) (Econst_int (Int.repr 1) tint) tuint)) (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _digit tint) (Econst_int (Int.repr 0) tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _t'14 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ecast (Etempvar _digit tint) tuint) (Ebinop Odiv (Ebinop Osub (Etempvar _t'14 tuint) (Etempvar _i tuint) tuint) (Etempvar _w tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Ebinop Omul (Etempvar _digit tint) (Etempvar _w tuint) tuint) tuint)) (Ssequence (Ssequence (Sifthenelse (Ebinop Ole (Etempvar _k tuint) (Etempvar _bias tuint) tint) (Ssequence (Sset _t'13 (Evar _tmin tuint)) (Sset _t'3 (Ecast (Etempvar _t'13 tuint) tuint))) (Ssequence (Sset _t'11 (Evar _tmax tuint)) (Sifthenelse  (Ebinop Oge (Etempvar _k tuint) (Ebinop Oadd (Etempvar _bias tuint) (Etempvar _t'11 tuint) tuint) tint) (Ssequence (Ssequence (Sset _t'12 (Evar _tmax tuint)) (Sset _t'3 (Ecast (Etempvar _t'12 tuint) tuint))) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint))) (Ssequence (Sset _t'3 (Ecast (Ebinop Osub (Etempvar _k tuint) (Etempvar _bias tuint) tuint) tuint)) (Sset _t'3 (Ecast (Etempvar _t'3 tuint) tuint)))))) (Sset _t (Etempvar _t'3 tuint))) (Ssequence (Sifthenelse (Ebinop Olt (Ecast (Etempvar _digit tint) tuint) (Etempvar _t tuint) tint) Sbreak Sskip) (Ssequence (Ssequence (Sset _t'9 (Evar _maxint tuint)) (Ssequence (Sset _t'10 (Evar _base tuint)) (Sifthenelse  (Ebinop Ogt (Etempvar _w tuint) (Ebinop Odiv (Etempvar _t'9 tuint) (Ebinop Osub (Etempvar _t'10 tuint) (Etempvar _t tuint) tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))) (Ssequence (Sset _t'8 (Evar _base tuint)) (Sset _w (Ebinop Omul (Etempvar _w tuint) (Ebinop Osub (Etempvar _t'8 tuint) (Etempvar _t tuint) tuint) tuint))))))))))))) (Ssequence (Sset _t'7 (Evar _base tuint)) (Sset _k (Ebinop Oadd (Etempvar _k tuint) (Etempvar _t'7 tuint) tuint))))) (Ssequence (Ssequence (Scall (Some _t'4) (Evar _adapt (Tfunction (tuint :: tuint :: tuint :: nil) tint cc_default)) ((Ebinop Osub (Etempvar _i tuint) (Etempvar _oldi tuint) tuint) :: (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) :: (Ebinop Oeq (Etempvar _oldi tuint) (Econst_int (Int.repr 0) tint) tint) :: nil)) (Sset _bias (Etempvar _t'4 tint))) (Ssequence (Ssequence (Sset _t'6 (Evar _maxint tuint)) (Sifthenelse (Ebinop Ogt (Ebinop Odiv (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) (Ebinop Osub (Etempvar _t'6 tuint) (Etempvar _n tuint) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip)) (Ssequence (Sset _n (Ebinop Oadd (Etempvar _n tuint) (Ebinop Odiv (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) tuint)) (Ssequence (Sset _i (Ebinop Omod (Etempvar _i tuint) (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint) tuint)) (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _written_out tuint) (Etempvar _max_out tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _gp_j (Etempvar _written_out tuint)) (Sloop (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _gp_j tuint) (Etempvar _i tuint) tint) Sskip Sbreak) (Ssequence (Sset _t'5 (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint) (tptr tuint)) tuint)) (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _gp_j tuint) (tptr tuint)) tuint) (Etempvar _t'5 tuint)))) (Sset _gp_j (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint)))) (Ssequence (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _i tuint) (tptr tuint)) tuint) (Etempvar _n tuint)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)) (Sset _written_out (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint))))))))))))))).

Lemma loop_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl,
  readable_share shi -> writable_share sho -> bytes_ok inp ->
  Zlength inp < Int.max_unsigned -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  Forall (fun c => c < 128) (sublist 0 (last_delim inp) inp) -> last_delim inp <= cap ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _processed_in (Vint (Int.repr (if last_delim inp =? 0 then 0 else last_delim inp + 1)));
     temp _written_out (Vint (Int.repr (last_delim inp)));
     temp _max_out (Vint (Int.repr cap)); temp _bias (Vint (Int.repr 72));
     temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
     temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
   SEP (puny_consts gv;
     arr0 shi tuchar (Zlength inp) (vb inp) pe;
     arr0 sho tuint cap (vb (sublist 0 (last_delim inp) inp) ++ sublist (last_delim inp) cap init) pd;
     data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_mainloop
  (overridePost
    (EX out: list Z,
     PROP (decode inp cap = (true, out))
     LOCAL (temp _written_out (Vint (Int.repr (Zlength out))); temp _pout_length pl)
     SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
    (dec_post gv shi pe inp sho pd cap init shl pl)).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl SH SH0 H LEN2 H1 H2 H3 H4.
assert (LEN: 0 <= Zlength inp) by apply Zlength_nonneg.
unfold stmt_mainloop, dec_post. abbreviate_semax.
forward.
forward_while (dec_inv gv shi pe inp sho pd cap init shl pl).
{ pose proof (last_delim_range inp) as LD.
  unfold dec_inv.
  Exists (if last_delim inp =? 0 then 0 else last_delim inp + 1) 128 0 72 (sublist 0 (last_delim inp) inp) (length inp).
  rewrite Zlength_sublist by lia.
  entailer!.
  rewrite <- decode_basic by auto. rewrite <- Zlength_correct.
  destruct (last_delim inp =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; repeat split; lia.
  apply derives_refl. }
{ entailer!. }
{ forward. forward.
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_seq.
  { apply (digits_block Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f); try lia; auto. }
  unfold dig_brk. Intros i1 pos1.
  apply (rest_block Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f i1 pos1); try lia; auto.
  unfold dec_inv. Intros pos' n' i' bias' out' f'. Exists (pos', n', i', bias', out', f'). simpl. entailer!. }
assert (DT: decode inp cap = (true, out))
  by (match goal with D: decode _ _ = steps _ _ _ _ _ _ _ _ |- _ => rewrite D end; apply steps_done; lia).
forward. Exists out. entailer!.
Qed.
