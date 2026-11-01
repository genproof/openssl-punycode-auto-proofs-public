(* pr_decode: the search of the last delimiter (for (j = 0; j < len; j++) ...). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Local Open Scope logic.

Lemma bytes_ok_Znth: forall l j, bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l <= 255.
Proof. intros. unfold bytes_ok in H. rewrite Forall_Znth in H. specialize (H j H0). simpl in H. rep_lia. Qed.

Lemma arr0_nz {cs: compspecs}: forall sh t n v p, n <> 0 -> arr0 sh t n v p = data_at sh (tarray t n) v p.
Proof. intros. unfold arr0. destruct (Z.eq_dec n 0); [contradiction | auto]. Qed.

Lemma delim_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd (R: ret_assert),
  readable_share shi -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _b (Vlong (Int64.repr 0)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin; arr0 sho tuint cap init pout; data_at shd t_dec (dec_rep 0 0) pd))
  stmt_delim
  (overridePost
    (PROP () LOCAL (temp _b (Vlong (Int64.repr (last_delim inp))); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
     SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin; arr0 sho tuint cap init pout; data_at shd t_dec (dec_rep 0 0) pd)) R).
Proof.
intros Espec shi pin inp sho pout cap init shd pd R SH H LEN2.
destruct R as [Rn Rb Rc Rr]. unfold stmt_delim, overridePost. abbreviate_semax.
set (len := Zlength inp) in *.
assert (LEN: 0 <= len) by apply Zlength_nonneg.
forward_for_simple_bound len (EX j: Z,
  PROP () LOCAL (temp _b (Vlong (Int64.repr (last_delim (sublist 0 j inp)))); temp _in pin; temp _len (Vlong (Int64.repr len)); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
  SEP (arr0 shi tuchar len (vb inp) pin; arr0 sho tuint cap init pout; data_at shd t_dec (dec_rep 0 0) pd)).
{ entailer!. }
{ assert (LNZ: len <> 0) by lia.
  pose proof (bytes_ok_Znth inp i H ltac:(lia)) as RX.
  rewrite (arr0_nz shi) by auto.
  forward.
  { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  assert (ZV: Znth i (vb inp) = Vint (Int.repr (Znth i inp))) by (unfold vb; rewrite Znth_map by (unfold len in *; lia); auto).
  change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV.
  forward_if.
  + forward. rewrite (arr0_nz shi) by auto. entailer!.
    rewrite last_delim_snoc by lia. rewrite (proj2 (Z.eqb_eq _ _)) by auto. auto.
  + forward. rewrite (arr0_nz shi) by auto. entailer!.
    rewrite last_delim_snoc by lia. rewrite (proj2 (Z.eqb_neq _ _)) by auto. auto. }
rewrite sublist_same by auto.
entailer!.
Qed.
