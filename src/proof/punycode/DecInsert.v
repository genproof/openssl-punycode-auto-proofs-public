(* ossl_punycode_decode: the I2 insertion loop (for (gp_j = written_out; gp_j > i; gp_j--) ...), a shift of
   the output so far by one position from i on. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.

Lemma shift_step': forall (A: list val) c j cap, 0 < j <= c -> c < cap -> Zlength A = cap ->
  upd_Znth j (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) cap A) (Znth (j - 1) A) =
  sublist 0 (j - 1 + 1) A ++ sublist (j - 1) c A ++ sublist (c + 1) cap A.
Proof. intros. subst. apply shift_step; lia. Qed.

Lemma shift_read': forall (out: list Z) (init: list val) c j cap, 0 < j <= c -> c < cap -> Zlength init = cap ->
  c = Zlength out ->
  let A := vb out ++ sublist c cap init in
  Znth (j - 1) (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) cap A) = Vint (Int.repr (Znth (j - 1) out)).
Proof. intros. subst A. subst c. unfold vb. list_solve. Qed.

Lemma shift_insert': forall (out: list Z) (init: list val) cap i x c, 0 <= i <= c -> c < cap ->
  Zlength init = cap -> c = Zlength out ->
  let A := vb out ++ sublist c cap init in
  upd_Znth i (sublist 0 (i + 1) A ++ sublist i c A ++ sublist (c + 1) cap A) (Vint (Int.repr x)) =
  vb (insert_at i x out) ++ sublist (c + 1) cap init.
Proof.
  intros. subst c. pose proof (shift_insert out init cap i x ltac:(lia) ltac:(lia) H1). simpl in H2.
  subst A. replace (Zlength (vb out ++ sublist (Zlength out) cap init)) with cap in H2 by (unfold vb; list_solve).
  rewrite H2. f_equal. f_equal. unfold insert_at. list_solve.
Qed.

Lemma insert_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl
  (out: list Z) (i2 n1 bias1 pos1: Z) (R: ret_assert),
  writable_share sho -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  0 <= i2 <= Zlength out -> Zlength out < cap ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _loop (Vint (Int.repr pos1)); temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1));
     temp _bias (Vint (Int.repr bias1)); temp _written_out (Vint (Int.repr (Zlength out)));
     temp _max_out (Vint (Int.repr cap)); gvars gv;
     temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; data_at sho (tarray tuint cap) ((vb out ++ sublist (Zlength out) cap init)) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_insert
  (overridePost (PROP () LOCAL (temp _loop (Vint (Int.repr pos1)); temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1));
     temp _bias (Vint (Int.repr bias1)); temp _written_out (Vint (Int.repr (Zlength out)));
     temp _max_out (Vint (Int.repr cap)); gvars gv;
     temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl) SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; data_at sho (tarray tuint cap) (sublist 0 (i2 + 1) (vb out ++ sublist (Zlength out) cap init) ++ sublist i2 (Zlength out) (vb out ++ sublist (Zlength out) cap init) ++ sublist (Zlength out + 1) cap (vb out ++ sublist (Zlength out) cap init)) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl)) R).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl out i2 n1 bias1 pos1 R SH0 CAP LI I2R CC.
destruct R as [Rn Rb Rc Rr]. unfold stmt_insert, overridePost. abbreviate_semax.
set (c := Zlength out) in *.
set (A := vb out ++ sublist c cap init).
assert (LA: Zlength A = cap) by (unfold A; rewrite Zlength_app, Zlength_vb, Zlength_sublist; lia).
forward.
forward_loop (EX j: Z,
    PROP (i2 <= j <= c)
    LOCAL (temp _gp_j (Vint (Int.repr j)); temp _loop (Vint (Int.repr pos1));
     temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1)); temp _bias (Vint (Int.repr bias1));
     temp _written_out (Vint (Int.repr c)); temp _max_out (Vint (Int.repr cap)); gvars gv;
     temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
    SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; data_at sho (tarray tuint cap) (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) cap A) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  continue: (EX j: Z,
    PROP (i2 < j <= c)
    LOCAL (temp _gp_j (Vint (Int.repr j)); temp _loop (Vint (Int.repr pos1));
     temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1)); temp _bias (Vint (Int.repr bias1));
     temp _written_out (Vint (Int.repr c)); temp _max_out (Vint (Int.repr cap)); gvars gv;
     temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
    SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; data_at sho (tarray tuint cap) (sublist 0 ((j - 1) + 1) A ++ sublist (j - 1) c A ++ sublist (c + 1) cap A) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  break: (PROP ()
    LOCAL (temp _loop (Vint (Int.repr pos1));
     temp _i (Vint (Int.repr i2)); temp _n (Vint (Int.repr n1)); temp _bias (Vint (Int.repr bias1));
     temp _written_out (Vint (Int.repr c)); temp _max_out (Vint (Int.repr cap)); gvars gv;
     temp _pEncoded pe; temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
    SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; data_at sho (tarray tuint cap) (sublist 0 (i2 + 1) A ++ sublist i2 c A ++ sublist (c + 1) cap A) pd;
    data_at shl tuint (Vint (Int.repr cap)) pl)).
{ Exists c. entailer!. rewrite <- LA. rewrite <- shift_init by lia. auto. }
{ Intros j.
  forward_if.
  { pose proof (shift_read' out init c j cap ltac:(lia) ltac:(lia) LI eq_refl) as RD. simpl in RD. fold A in RD.
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite RD. simpl. auto. }
    change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite RD.
    forward.
    Exists j. entailer!.
    assert (RA: Znth (j - 1) A = Vint (Int.repr (Znth (j - 1) out)))
      by (unfold A, vb; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; auto).
    rewrite <- RA. rewrite shift_step' by (auto; lia). auto. }
  { forward. replace j with i2 by lia. entailer!. } }
{ Intros j. forward. Exists (j - 1). entailer!. }
apply andp_left2. apply derives_refl.
Qed.
