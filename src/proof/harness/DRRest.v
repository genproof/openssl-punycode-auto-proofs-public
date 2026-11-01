(* pr_decode: the end of one iteration of the main loop (adapt, n, i, the output check, the insertion). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Local Open Scope logic.
Require Import OpensslPunycode.proof.harness.DRInsert.

Lemma add64_repr: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma divu64_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 < b <= Int64.max_unsigned ->
  Int64.divu (Int64.repr a) (Int64.repr b) = Int64.repr (a / b).
Proof. intros. unfold Int64.divu. rewrite !Int64.unsigned_repr by lia. auto. Qed.

Lemma modu64_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 < b <= Int64.max_unsigned ->
  Int64.modu (Int64.repr a) (Int64.repr b) = Int64.repr (a mod b).
Proof. intros. unfold Int64.modu. rewrite !Int64.unsigned_repr by lia. auto. Qed.

Lemma rest_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd
  (pos n i bias: Z) (out: list Z) (f: nat) (i1 pos1: Z) (I J: environ -> mpred),
  readable_share shi -> writable_share sho -> writable_share shd -> bytes_ok inp ->
  Zlength inp < Int.max_unsigned -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  0 <= Zlength out <= pos -> pos < Zlength inp -> Zlength out <= cap -> 0 <= i <= Zlength out ->
  128 <= n <= maxint -> Zlength inp - pos <= Z.of_nat f ->
  decode inp cap = steps inp f cap pos n i bias out ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1) ->
  i <= i1 <= maxint -> pos < pos1 <= Zlength inp ->
  (dr_inv shi pin inp sho pout cap init shd pd |-- I) ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _oldi (Vlong (Int64.repr i)); temp _pos (Vlong (Int64.repr pos1)); temp _i (Vlong (Int64.repr i1));
     temp _n (Vlong (Int64.repr n)); temp _bias (Vlong (Int64.repr bias)); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd))
  stmt_rest
  (loop1_ret_assert I (overridePost J (dr_post shi pin inp sho pout cap init shd pd))).
Proof.
intros Espec shi pin inp sho pout cap init shd pd pos n i bias out f i1 pos1 I J
  SH SH0 SH1 H LEN2 CAP LI LO POS LOC RI RN FUEL DEC DG RI1 POS1 HI.
destruct (steps_some inp f cap pos n i bias out i1 pos1 POS FUEL DG) as [f' [FUEL' DEC2]].
rewrite DEC2 in DEC. clear DEC2. cbv zeta in DEC.
unfold stmt_rest, dr_post. abbreviate_semax.
set (c := Zlength out) in *.
unfold dec_rep.
forward.
forward_call (i1 - i, c + 1, if i =? 0 then 1 else 0).
{ entailer!. simpl. destruct (i =? 0) eqn:E; [apply Z.eqb_eq in E; subst; reflexivity | apply Z.eqb_neq in E].
  rewrite Int64.eq_false; auto. intro X. apply repr_inj_unsigned64 in X; unfold maxint in *; rep_lia. }
{ unfold maxint in *. destruct (i =? 0); rep_lia. }
replace (negb ((if i =? 0 then 1 else 0) =? 0)) with (i =? 0) by (destruct (i =? 0); reflexivity).
set (bias1 := adapt (i1 - i) (c + 1) (i =? 0)) in *.
pose proof (adapt_bound (i1 - i) (c + 1) (i =? 0) ltac:(lia) ltac:(lia)) as AB. fold bias1 in AB.
forward.
{ entailer!. change (Int.signed (Int.repr 1)) with 1 in *. change Int64.zero with (Int64.repr 0) in *.
  match goal with C: Int64.repr _ = Int64.repr 0 |- _ => apply repr_inj_unsigned64 in C; rep_lia end. }
change (Int.signed (Int.repr 1)) with 1.
rewrite add64_repr, divu64_repr, add64_repr by (unfold maxint in *; rep_lia).
assert (I1D: 0 <= i1 / (c + 1) <= i1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
set (n1 := n + i1 / (c + 1)) in *.
forward_if.
{ match goal with C: Int64.ltu _ _ = true |- _ => unfold Int64.ltu in C;
    rewrite !Int64.unsigned_repr in C by (unfold maxint in *; rep_lia); destruct zlt in C; [ | discriminate] end.
  rewrite (proj2 (Z.ltb_lt _ _)) in DEC by (unfold maxint; lia).
  forward. rewrite DEC. simpl. entailer!; apply derives_refl. }
match goal with C: Int64.ltu _ _ = false |- _ => unfold Int64.ltu in C;
  rewrite !Int64.unsigned_repr in C by (unfold maxint in *; rep_lia); destruct zlt in C; [discriminate | ] end.
rewrite (proj2 (Z.ltb_ge _ _)) in DEC by (unfold maxint; lia).
forward.
{ entailer!. change Int64.zero with (Int64.repr 0) in *. change (Int.signed (Int.repr 1)) with 1 in *.
  match goal with C: Int64.repr _ = Int64.repr 0 |- _ => apply repr_inj_unsigned64 in C; rep_lia end. }
change (Int.signed (Int.repr 1)) with 1.
rewrite add64_repr, modu64_repr by (unfold maxint in *; rep_lia).
set (i2 := i1 mod (c + 1)) in *.
assert (I2R: 0 <= i2 < c + 1) by (apply Z.mod_pos_bound; lia).
forward_if.
{   rewrite (proj2 (Z.leb_le _ _)) in DEC by lia.
  forward. rewrite DEC. simpl. entailer!; apply derives_refl. }
rewrite (proj2 (Z.leb_gt _ _)) in DEC by lia.
assert (ZL: Zlength (insert_at i2 n1 out) = c + 1)
  by (unfold insert_at; rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia; lia).
eapply semax_post_flipped.
{ eapply semax_pre; [ | apply (insert_block Espec shi pin inp sho pout cap init shd pd
    out i2 n1 bias1 pos1); auto; unfold maxint in *; lia ].
  unfold dec_rep. entailer!. apply derives_refl. }
{ simpl RA_normal. eapply derives_trans; [ | apply HI ]. unfold dr_inv.
  Exists pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out) f'. rewrite ZL.
  entailer!. unfold maxint in *. repeat split; lia. apply derives_refl. }
all: intros; simpl; normalize.
Qed.