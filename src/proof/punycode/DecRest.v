(* ossl_punycode_decode: the end of one iteration of the main loop (adapt, the n and output checks, the I2
   insertion, the store of n). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.
Require Import OpensslPunycode.proof.punycode.DecArith.
Require Import OpensslPunycode.proof.punycode.DecRestB.



Lemma rest_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (pos n i bias: Z) (out: list Z) (f: nat) (i1 pos1: Z) (I J: environ -> mpred),
  readable_share shi -> writable_share sho -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  0 <= Zlength out <= pos -> pos < Zlength inp -> Zlength out <= cap -> 0 <= i <= Zlength out ->
  128 <= n <= Int.max_unsigned -> Zlength inp - pos <= Z.of_nat f ->
  decode inp cap = steps inp f cap pos n i bias out ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1) ->
  i <= i1 <= Int.max_unsigned -> pos < pos1 <= Zlength inp ->
  (dec_inv gv shi pe inp sho pd cap init shl pl |-- I) ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _oldi (Vint (Int.repr i)); temp _loop (Vint (Int.repr pos1)); temp _i (Vint (Int.repr i1));
    temp _n (Vint (Int.repr n)); temp _bias (Vint (Int.repr bias));
    temp _written_out (Vint (Int.repr (Zlength out))); temp _max_out (Vint (Int.repr cap)); gvars gv;
    temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
   SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_rest
  (loop1_ret_assert I (overridePost J (dec_post gv shi pe inp sho pd cap init shl pl))).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl pos n i bias out f i1 pos1 I J
  SH SH0 H LEN2 CAP LI LO POS LOC RI RN FUEL DEC DG RI1 POS1 HI.
destruct (steps_some inp f cap pos n i bias out i1 pos1 POS FUEL DG) as [f' [FUEL' DEC2]].
rewrite DEC2 in DEC. clear DEC2. cbv zeta in DEC.
unfold stmt_rest, dec_post. abbreviate_semax.
set (c := Zlength out) in *.
forward_call (gv, i1 - i, c + 1, if i =? 0 then 1 else 0).
{ entailer!. destruct (i =? 0) eqn:E; [apply Z.eqb_eq in E; subst i | apply Z.eqb_neq in E].
  - rewrite Int.eq_true. auto.
  - rewrite Int.eq_false; auto. intro X. apply repr_inj_unsigned in X; rep_lia. }
{ destruct (i =? 0); rep_lia. }
replace (negb ((if i =? 0 then 1 else 0) =? 0)) with (i =? 0) by (destruct (i =? 0); reflexivity).
set (bias1 := adapt (i1 - i) (c + 1) (i =? 0)) in *.
pose proof (adapt_bound (i1 - i) (c + 1) (i =? 0) ltac:(lia) ltac:(lia)) as AB. fold bias1 in AB.
unfold puny_consts. Intros.
forward.
forward_if.
{ entailer!. match goal with C: Int.repr _ = Int.zero |- _ => revert C end. apply repr_nonzero; rep_lia. }
{ match goal with C: Int.unsigned (Int.repr (-1 - n)) < _ |- _ =>
    rewrite unsigned_m1_sub, divu_unsigned in C by rep_lia; rename C into NN end.
  rewrite (proj2 (Z.ltb_lt _ _)) in DEC by lia.
  forward. rewrite (decode_result_eq _ _ _ false out LEN2 DEC). cbn [fst snd].
  unfold puny_consts. entailer!. apply derives_refl. }
match goal with C: Int.unsigned (Int.repr (-1 - n)) >= _ |- _ =>
  rewrite unsigned_m1_sub, divu_unsigned in C by rep_lia; rename C into NN end.
rewrite (proj2 (Z.ltb_ge _ _)) in DEC by lia.
set (n1 := n + i1 / (c + 1)) in *.
assert (I1D: 0 <= i1 / (c + 1)) by (apply Z.div_pos; lia).
forward.
{ entailer!. match goal with C: Int.repr _ = Int.zero |- _ => revert C end. apply repr_nonzero; rep_lia. }
forward.
{ entailer!. match goal with C: Int.repr _ = Int.zero |- _ => revert C end. apply repr_nonzero; rep_lia. }
rewrite add_repr, divu_repr, add_repr, modu_repr by rep_lia.
set (i2 := i1 mod (c + 1)) in *.
assert (I2R: 0 <= i2 < c + 1) by (apply Z.mod_pos_bound; lia).
eapply semax_pre; [ | apply (rest_b_block Espec gv shi pe inp sho pd cap init shl pl pos out f' i2 n1 bias1 pos1 I J);
  auto; try lia; unfold maxint in *; rep_lia ].
unfold puny_consts. entailer!. apply derives_refl.
Qed.
