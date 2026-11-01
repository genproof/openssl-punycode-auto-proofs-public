(* pr_decode: the insertion of n at position i (the shift loop for (j = outlen; j > i; j--), the store, the
   count). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Local Open Scope logic.

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

Lemma insert_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd
  (out: list Z) (i2 n1 bias1 pos1: Z),
  writable_share sho -> writable_share shd -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  0 <= i2 <= Zlength out -> Zlength out < cap -> 0 <= n1 <= maxint ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _i (Vlong (Int64.repr i2)); temp _outlen (Vlong (Int64.repr (Zlength out)));
     temp _pos (Vlong (Int64.repr pos1)); temp _n (Vlong (Int64.repr n1));
     temp _bias (Vlong (Int64.repr bias1)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd))
  stmt_insert
  (normal_ret_assert
   (PROP ()
    LOCAL (temp _i (Vlong (Int64.repr (i2 + 1)));
      temp _pos (Vlong (Int64.repr pos1)); temp _n (Vlong (Int64.repr n1));
      temp _bias (Vlong (Int64.repr bias1)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
    SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb (insert_at i2 n1 out) ++ sublist (Zlength out + 1) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out + 1)) pd))).
Proof.
intros Espec shi pin inp sho pout cap init shd pd out i2 n1 bias1 pos1 SH0 SH1 CAP LI I2R CC NR.
unfold stmt_insert. abbreviate_semax.
pose proof (Zlength_nonneg out) as LO.
set (c := Zlength out) in *.
set (A := vb out ++ sublist c cap init).
assert (LA: Zlength A = cap) by (unfold A; rewrite Zlength_app, Zlength_vb, Zlength_sublist; lia).
change (arr0 sho tuint cap A pout) with (if Z.eq_dec cap 0 then emp else data_at sho (tarray tuint cap) A pout).
destruct (Z.eq_dec cap 0); [lia | ].
forward.
forward_loop (EX j: Z,
    PROP (i2 <= j <= c)
    LOCAL (temp _j (Vlong (Int64.repr j)); temp _i (Vlong (Int64.repr i2)); temp _outlen (Vlong (Int64.repr c));
     temp _pos (Vlong (Int64.repr pos1)); temp _n (Vlong (Int64.repr n1));
     temp _bias (Vlong (Int64.repr bias1)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
     temp _cap (Vlong (Int64.repr cap)); temp _d pd)
    SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
     data_at sho (tarray tuint cap) (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) cap A) pout;
     data_at shd t_dec (dec_rep 0 c) pd))
  break: (PROP ()
    LOCAL (temp _i (Vlong (Int64.repr i2)); temp _outlen (Vlong (Int64.repr c));
     temp _pos (Vlong (Int64.repr pos1)); temp _n (Vlong (Int64.repr n1));
     temp _bias (Vlong (Int64.repr bias1)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
     temp _cap (Vlong (Int64.repr cap)); temp _d pd)
    SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
     data_at sho (tarray tuint cap) (sublist 0 (i2 + 1) A ++ sublist i2 c A ++ sublist (c + 1) cap A) pout;
     data_at shd t_dec (dec_rep 0 c) pd)).
{ Exists c. entailer!. rewrite <- LA. rewrite <- shift_init by lia. auto. }
{ Intros j.
  forward_if.
  { assert (JI: i2 < j) by lia.
    pose proof (shift_read' out init c j cap ltac:(lia) ltac:(lia) LI eq_refl) as RD. simpl in RD. fold A in RD.
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val).
      try rewrite Int64.sub_signed, !Int64.signed_repr by rep_lia. rewrite RD. simpl. auto. }
    change (@Znth val Vundef) with (@Znth val Inhabitant_val).
    try rewrite Int64.sub_signed, !Int64.signed_repr by rep_lia. rewrite RD.
    forward.
    forward.
    Exists (j - 1). entailer!.
    assert (RA: Znth (j - 1) A = Vint (Int.repr (Znth (j - 1) out)))
      by (unfold A, vb; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; auto).
    rewrite <- RA. rewrite shift_step' by (auto; lia). auto. }
  { assert (JI: j <= i2) by lia.
    forward. replace j with i2 by lia. entailer!. } }
forward.
forward.
forward.
change (Int.signed (Int.repr 1)) with 1.
rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold maxint in NR; rep_lia).
pose proof (shift_insert' out init cap i2 n1 c I2R CC LI eq_refl) as SI. simpl in SI. fold A in SI. rewrite SI.
assert (AZ: forall v, arr0 sho tuint cap v pout = data_at sho (tarray tuint cap) v pout)
  by (intros; unfold arr0; destruct (Z.eq_dec cap 0); [lia|auto]).
rewrite AZ. unfold dec_rep. simpl fst. rewrite !Int64.add_signed, !Int64.signed_repr by rep_lia.
entailer!.
Qed.
