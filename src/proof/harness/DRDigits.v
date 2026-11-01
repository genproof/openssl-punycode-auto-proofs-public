(* pr_decode: the digit loop of one delta (for (;;) {...}). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Require Import OpensslPunycode.proof.harness.DRDelim.
Require OpensslPunycode.proof.harness.RefRt.
Local Open Scope logic.

Lemma dig_add64_repr: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma dig_mul64_repr: forall a b, Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_mult; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma dig_sub64_repr: forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Ltac ltu64 := match goal with C: Int64.ltu _ _ = _ |- _ => unfold Int64.ltu in C;
  rewrite !Int64.unsigned_repr in C by (unfold maxint in *; rep_lia); destruct zlt in C; try discriminate end.

Lemma digits_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd
  (pos n i bias: Z) (out: list Z) (f: nat) (I J: environ -> mpred),
  readable_share shi -> bytes_ok inp -> Zlength inp < Int.max_unsigned ->
  0 <= pos < Zlength inp -> 0 <= i <= maxint -> 0 <= bias <= 2340 ->
  Zlength inp - pos <= Z.of_nat f -> decode inp cap = steps inp f cap pos n i bias out ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _k (Vlong (Int64.repr 36)); temp _w (Vlong (Int64.repr 1)); temp _oldi (Vlong (Int64.repr i));
     temp _pos (Vlong (Int64.repr pos)); temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
     temp _bias (Vlong (Int64.repr bias)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd))
  stmt_digits
  (overridePost (dig_brk shi pin inp sho pout cap init shd pd pos n i bias out)
   (loop1_ret_assert I (overridePost J (dr_post shi pin inp sho pout cap init shd pd)))).
Proof.
intros Espec shi pin inp sho pout cap init shd pd pos n i bias out f I J
  SH H LEN2 POS RI RB FUEL DEC.
unfold stmt_digits, dr_post. abbreviate_semax.
assert (LNZ: Zlength inp <> 0) by lia.
rewrite (arr0_nz shi) by auto.
forward_loop (dig_inv shi pin inp sho pout cap init shd pd pos n i bias out)
  break: (dig_brk shi pin inp sho pout cap init shd pd pos n i bias out).
{ unfold dig_inv. Exists pos i 1 0. rewrite (arr0_nz shi) by auto. entailer!. }
{ unfold dig_inv. Intros p i' w j. rewrite (arr0_nz shi) by auto.
  rename H0 into DG.
  forward_if.
  { assert (DF: decode inp cap = (false, out))
      by (rewrite DEC; apply steps_none; try lia; rewrite DG; apply digits_end; lia).
    forward. rewrite DF. simpl. rewrite (arr0_nz shi) by auto. entailer!. }
  pose proof (bytes_ok_Znth inp p H ltac:(lia)) as RX.
  assert (ZV: Znth p (vb inp) = Vint (Int.repr (Znth p inp))) by (unfold vb; rewrite Znth_map by lia; auto).
  forward.
  { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV. simpl.
    rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite ZV.
  forward_call (Znth p inp).
  set (d := digit_value (Znth p inp)) in *.
  pose proof (digit_value_range (Znth p inp)) as DR. fold d in DR.
  rewrite (digits_step inp p i' w (36 * (j + 1)) bias) in DG by lia. cbv zeta in DG. fold d in DG.
  forward.
  forward.
  change (Int.signed (Int.repr 1)) with 1. rewrite dig_add64_repr.
  forward_if.
  { assert (DF: decode inp cap = (false, out)).
    { rewrite DEC; apply steps_none; try lia. rewrite DG. rewrite (proj2 (Z.leb_le 36 d)) by lia. auto. }
    forward. rewrite DF. simpl. rewrite (arr0_nz shi) by auto. entailer!. }
  rewrite (proj2 (Z.leb_gt 36 d)) in DG by lia.
  forward.
  rewrite dig_mul64_repr, dig_add64_repr.
  assert (DW: 0 <= d * w <= 35 * maxint) by (unfold maxint in *; nia).
  forward_if.
  { try ltu64. assert (DF: decode inp cap = (false, out)).
    { rewrite DEC; apply steps_none; try lia. rewrite DG. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold maxint in *; lia). auto. }
    forward. rewrite DF. simpl. rewrite (arr0_nz shi) by auto. entailer!. }
  try ltu64. rewrite (proj2 (Z.ltb_ge _ _)) in DG by (unfold maxint in *; lia).
  forward_call ((36 * (j + 1))%Z, bias).
  set (t := threshold (36 * (j + 1)) bias) in *.
  pose proof (threshold_range (36 * (j + 1)) bias) as TR. fold t in TR.
  forward_if.
  { try ltu64. forward.
    unfold dig_brk. Exists (i' + d * w)%Z (p + 1). rewrite (arr0_nz shi) by auto.
    rewrite (proj2 (Z.ltb_lt _ _)) in DG by lia.
    entailer!. unfold maxint in *. lia. }
  try ltu64. rewrite (proj2 (Z.ltb_ge _ _)) in DG by lia.
  forward.
  rewrite dig_sub64_repr, dig_mul64_repr.
  assert (WT: 0 <= w * (36 - t) <= 35 * maxint) by (unfold maxint in *; nia).
  forward_if.
  { try ltu64. assert (DF: decode inp cap = (false, out)).
    { rewrite DEC; apply steps_none; try lia. rewrite DG. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold maxint in *; lia). auto. }
    forward. rewrite DF. simpl. rewrite (arr0_nz shi) by auto. entailer!. }
  try ltu64. rewrite (proj2 (Z.ltb_ge _ _)) in DG by (unfold maxint in *; lia).
  forward.
  unfold dig_inv. Exists (p + 1) (i' + d * w)%Z (w * (36 - t))%Z (j + 1).
  rewrite (arr0_nz shi) by auto. rewrite dig_add64_repr.
  replace (36 * (j + 1) + 36)%Z with (36 * (j + 1 + 1))%Z in * by lia.
  entailer!. unfold maxint in *. nia. }
Qed.