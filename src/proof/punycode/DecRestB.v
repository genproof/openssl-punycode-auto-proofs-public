(* ossl_punycode_decode: the end of one iteration of the main loop (the output check, the I2 insertion
   (DecInsert), the store of n, i++ and written_out++). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecArith.
Require Import OpensslPunycode.proof.punycode.DecInsert.

Definition stmt_rest_b : statement := (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _written_out tuint) (Etempvar _max_out tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip) (Ssequence (Ssequence (Sset _gp_j (Etempvar _written_out tuint)) (Sloop (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _gp_j tuint) (Etempvar _i tuint) tint) Sskip Sbreak) (Ssequence (Sset _t'5 (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint) (tptr tuint)) tuint)) (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _gp_j tuint) (tptr tuint)) tuint) (Etempvar _t'5 tuint)))) (Sset _gp_j (Ebinop Osub (Etempvar _gp_j tuint) (Econst_int (Int.repr 1) tint) tuint)))) (Ssequence (Sassign (Ederef (Ebinop Oadd (Etempvar _pDecoded (tptr tuint)) (Etempvar _i tuint) (tptr tuint)) tuint) (Etempvar _n tuint)) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)) (Sset _written_out (Ebinop Oadd (Etempvar _written_out tuint) (Econst_int (Int.repr 1) tint) tuint)))))).

Lemma Zlength_insert_at: forall i x (l: list Z), 0 <= i <= Zlength l -> Zlength (insert_at i x l) = Zlength l + 1.
Proof. intros. unfold insert_at. list_solve. Qed.

Lemma arr0_tuint_nz {cs: compspecs}: forall sh n (v: list val) p, n <> 0 ->
  arr0 sh tuint n v p = data_at sh (tarray tuint n) v p.
Proof. intros. unfold arr0. rewrite if_false by auto. auto. Qed.

Lemma rest_b_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos: Z) (out: list Z) (f': nat) (i2 n1 bias1 pos1: Z) (I J: environ -> mpred),
  writable_share sho -> Zlength inp < Int.max_unsigned ->
  0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  0 <= Zlength out <= pos -> pos < pos1 <= Zlength inp -> Zlength out <= cap -> 0 <= i2 <= Zlength out ->
  128 <= n1 <= Int.max_unsigned -> 0 <= bias1 <= 2340 -> Zlength inp - pos - 1 <= Z.of_nat f' ->
  decode inp cap = (if cap <=? Zlength out then (false, out)
                    else steps inp f' cap pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out)) ->
  (dec_inv gv shi pe inp sho pd cap init shl pl |-- I) ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1)); temp _bias (Vint (Int.repr bias1));
    temp _loop (Vint (Int.repr pos1)); temp _written_out (Vint (Int.repr (Zlength out)));
    temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_rest_b
  (loop1_ret_assert I (overridePost J (dec_post gv shi pe inp sho pd cap init shl pl))).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos out f' i2 n1 bias1 pos1 I J
  SH0 LEN2 CAP LI LO POS1 LOC I2R RN AB FUEL' DEC HI.
unfold stmt_rest_b, dec_post. abbreviate_semax.
set (c := Zlength out) in *.
forward_if.
{
  rewrite (proj2 (Z.leb_le _ _)) in DEC by lia.
  forward. rewrite (decode_result_eq _ _ _ false out LEN2 DEC). cbn [fst snd].
  unfold puny_consts. entailer!. apply derives_refl. }
match goal with C: c < cap |- _ => rename C into CC end.
rewrite (proj2 (Z.leb_gt _ _)) in DEC by lia.
unfold arr0 at 2. rewrite if_false by lia.
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ eapply semax_pre; [ | apply (insert_block Espec gv shi pe inp sho pd cap init shl pl out i2 n1 bias1 pos1); auto; lia ].
  unfold puny_consts. entailer!. }
fold c.
set (A := vb out ++ sublist c cap init).
forward.
pose proof (shift_insert' out init cap i2 n1 c ltac:(lia) ltac:(lia) LI eq_refl) as SI. simpl in SI. fold A in SI.
rewrite SI.
forward. forward.
eapply derives_trans; [ | apply HI ].
unfold dec_inv.
Exists pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out) f'.
rewrite Zlength_insert_at by lia. fold c.
rewrite (arr0_tuint_nz sho cap) by lia.
entailer!.
all: unfold maxint in *; rep_lia.
Qed.
