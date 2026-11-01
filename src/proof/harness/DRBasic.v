(* pr_decode: the copy of the basic code points before the last delimiter (for (j = 0; j < b; j++) ...). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Require Import OpensslPunycode.proof.harness.DRDelim.
Local Open Scope logic.

Lemma basic_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd,
  readable_share shi -> writable_share sho -> writable_share shd -> bytes_ok inp ->
  Zlength inp < Int.max_unsigned -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  last_delim inp <= cap ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP () LOCAL (temp _b (Vlong (Int64.repr (last_delim inp))); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin; arr0 sho tuint cap init pout; data_at shd t_dec (dec_rep 0 0) pd))
  stmt_basic
  (overridePost
    (PROP (Forall (fun c => c < 128) (sublist 0 (last_delim inp) inp))
     LOCAL (temp _b (Vlong (Int64.repr (last_delim inp))); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
     SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
          arr0 sho tuint cap (vb (sublist 0 (last_delim inp) inp) ++ sublist (last_delim inp) cap init) pout;
          data_at shd t_dec (dec_rep 0 (last_delim inp)) pd))
    (dr_post shi pin inp sho pout cap init shd pd)).
Proof.
intros Espec shi pin inp sho pout cap init shd pd SH SH0 SH1 H LEN2 CAP LI LDC.
unfold stmt_basic, dr_post. abbreviate_semax.
pose proof (last_delim_range inp) as LD.
set (b := last_delim inp) in *.
assert (LEN: 0 <= Zlength inp) by apply Zlength_nonneg.
forward_for_simple_bound b (EX j: Z,
  PROP (Forall (fun c => c < 128) (sublist 0 j inp))
  LOCAL (temp _b (Vlong (Int64.repr b)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
  SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb (sublist 0 j inp) ++ sublist j cap init) pout;
       data_at shd t_dec (dec_rep 0 j) pd)).
{ entailer!. rewrite sublist_nil, sublist_same by lia. simpl. auto. }
{ assert (LNZ: Zlength inp <> 0) by lia.
  assert (CNZ: cap <> 0) by lia.
  pose proof (bytes_ok_Znth inp i H ltac:(lia)) as RX.
  rewrite (arr0_nz shi) by auto. rewrite (arr0_nz sho) by auto.
  assert (ZV: Znth i (vb inp) = Vint (Int.repr (Znth i inp))) by (unfold vb; rewrite Znth_map by lia; auto).
  forward.
  { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV. simpl.
    rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV.
  forward_if.
  { assert (DF: decode inp cap = (false, sublist 0 i inp))
      by (apply decode_fail_basic; auto; lia).
    forward.
    rewrite DF. simpl. rewrite Zlength_sublist by lia. replace (i - 0) with i by lia.
    rewrite (arr0_nz shi) by auto. rewrite (arr0_nz sho) by auto. unfold dec_rep.
    entailer!. }
  forward.
  { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV. simpl.
    rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV.
  forward.
  forward.
  entailer!.
  { apply Forall_sublist_snoc; auto; lia. }
  rewrite (arr0_nz shi) by auto. rewrite (arr0_nz sho) by auto. unfold dec_rep.
  rewrite basic_store by lia.
  entailer!. }
entailer!.
Qed.
