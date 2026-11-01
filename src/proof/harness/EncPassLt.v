(* pr_encode: one iteration of the pass, after the code point c is loaded: the case c < n. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Lemma kont_lt: forall cps f n c rest d bi h b out, c < n ->
  kont cps f n (c :: rest) d bi h b out = if maxint <? d + 1 then None else kont cps f n rest (d + 1) bi h b out.
Proof.
  intros. unfold kont. cbn [enc_pass]. replace (c <? n) with true by lia.
  destruct (maxint <? d + 1); auto.
Qed.

Lemma kont_eq: forall cps f n rest d bi h b out,
  kont cps f n (n :: rest) d bi h b out =
  kont cps f n rest 0 (adapt d (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 d 36 bi).
Proof. intros. unfold kont. cbn [enc_pass]. rewrite Z.ltb_irrefl, Z.eqb_refl. auto. Qed.

Lemma kont_gt: forall cps f n c rest d bi h b out, n < c ->
  kont cps f n (c :: rest) d bi h b out = kont cps f n rest d bi h b out.
Proof.
  intros. unfold kont. cbn [enc_pass]. replace (c <? n) with false by lia. replace (c =? n) with false by lia.
  auto.
Qed.

Lemma cnt_eq_succ: forall n (l: list Z) j, 0 <= j < Zlength l ->
  cnt_eq n (sublist 0 (j + 1) l) = cnt_eq n (sublist 0 j l) + (if Znth j l =? n then 1 else 0).
Proof.
  intros. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite cnt_eq_app, sublist_len_1 by lia.
  rewrite cnt_eq_one. auto.
Qed.

Ltac fix_eq64 := match goal with H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
  apply Int64.same_if_eq in H; apply (f_equal Int64.unsigned) in H;
  rewrite !Int64.unsigned_repr in H by (unfold maxint in *; rep_lia) end.

Lemma HoP: forall Q R, RA_normal (overridePost Q R) = Q.
Proof. intros Q R; destruct R; reflexivity. Qed.

Lemma brk_post {cs: compspecs}: forall Delta Q X F R,
  ENTAIL Delta, RA_break (overridePost Q (frame_ret_assert (function_body_ret_assert tint X) F)) |-- R.
Proof. intros. simpl. intro rho. apply andp_left2. normalize. Qed.

Lemma cont_post {cs: compspecs}: forall Delta Q X F R,
  ENTAIL Delta, RA_continue (overridePost Q (frame_ret_assert (function_body_ret_assert tint X) F)) |-- R.
Proof. intros. simpl. intro rho. apply andp_left2. normalize. Qed.

Definition stmt_passrest := (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _c tulong)
                                                         (Etempvar _n tulong)
                                                         tint)
                                            (Ssequence
                                              (Sset _delta
                                                (Ebinop Oadd
                                                  (Etempvar _delta tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _delta tulong)
                                                             (Econst_long (Int64.repr 4294967295) tulong)
                                                             tint)
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                Sskip))
                                            Sskip)
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _c tulong)
                                                         (Etempvar _n tulong)
                                                         tint)
                                            stmt_digs
                                            Sskip)).

Lemma enc_pass_lt: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (f: nat) (n h0 B j c delta bias h: Z)
  (out: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  0 <= j < Zlength cps -> 0 <= h0 <= Zlength cps -> 0 <= B <= Int.max_unsigned -> 0 <= n <= maxint ->
  c < n ->
  encode cps = kont cps f n (c :: sublist (j + 1) (Zlength cps) cps) delta bias h B out ->
  h = h0 + cnt_eq n (sublist 0 j cps) -> 0 <= delta <= maxint -> 0 <= bias <= 2400 -> Zlength out <= ocap ->
  0 <= c <= Int.max_unsigned ->
  cnt_eq n (sublist 0 (j + 1) cps) = cnt_eq n (sublist 0 j cps) + (if c =? n then 1 else 0) ->
  cnt_eq n (sublist 0 j cps) <= j - 0 -> 0 <= cnt_eq n (sublist 0 j cps) ->
  semax DeltaE
   (PROP () LOCAL (temp _c (Vlong (Int64.repr c)); temp _t'7 (Vint (Int.repr c));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_passrest
   (overridePost (pass_st shc pc cps sho po ocap oinit shl pl f n h0 B (j + 1) j)
      (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros until out. intros H H0 H1 H3 H4 H5 H6 H7 H8 H9 Hlt Hk Hh Hd Hb Ho Hc Hcnt Hcl Hcn0.
  pose proof (Zlength_nonneg out) as Hol.
  unfold stmt_passrest, pass_st, enc_post. abbreviate_semax.
rewrite kont_lt in Hk by lia.
  forward_if (PROP (delta + 1 <= maxint)
    LOCAL (temp _c (Vlong (Int64.repr c)); temp _n (Vlong (Int64.repr n));
      temp _delta (Vlong (Int64.repr (delta + 1))); temp _bias (Vlong (Int64.repr bias));
      temp _out (Vlong (Int64.repr (Zlength out))); temp _b (Vlong (Int64.repr B));
      temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j)); temp _cps pc;
      temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po; temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
      data_at_ shl tulong pl)).
  { forward.
    forward_if.
    + forward. fix_cmp. apply ret0_entail; [ | apply bufv_len; lia].
      apply encode_fits_none. rewrite Hk. replace (maxint <? delta + 1) with true by (unfold maxint in *; lia). auto.
    + forward. entailer!. fix_cmp. unfold maxint; lia. }
  { fix_cmp. lia. }
  Intros. replace (maxint <? delta + 1) with false in Hk by lia.
  forward_if.
  + fix_eq64. lia.
  + forward. Exists (delta + 1) bias h out. entailer!.
    rewrite Hcnt. replace (c =? n) with false by lia. lia.
Qed.
