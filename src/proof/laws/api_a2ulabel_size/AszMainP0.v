(* Piece 0 of the main of harness/api_a2ulabel_size.c (AszMainDefs): len and the input in, biglen and big, outlen and
   out (each from any_bytes), the NULL test (with outlen == 0), in[len] = 0 and the reset of the shim's failure
   flag. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainDefs.
Local Open Scope logic.

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* A block of octets from any_bytes that may be NULL: its token and its contents, each emp when it is NULL.  Kept
   folded in the NULL test: VST's automation is slow on the conditionals of the unfolded form. *)
Definition atok {cs: compspecs} (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p.
Definition adat {cs: compspecs} (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp else data_at Ews (tarray tuchar n) v p.

Lemma asplit {cs: compspecs} n v p:
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)
  |-- atok n p * adat n v p.
Proof.
  unfold atok, adat. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | auto ].
Qed.

(* The test p == NULL of such a block is defined. *)
Lemma ablock_tc {cs: compspecs} n v p P:
  0 <= n ->
  atok n p * adat n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold atok, adat. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray tuchar 0) p). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray tuchar n) v p);
        [ apply readable_nonidentity; auto | simpl; rewrite Z.max_r by lia; lia | ].
      entailer!.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

(* A non-NULL block of any_bytes as ossl_a2ulabel's out buffer (the token of a zero-size block kept as tk0's). *)
Lemma aout_buf q n ob:
  q <> nullval ->
  @atok CCS n q * @adat CCS n (vb ob) q
  |-- OpensslPunycode.proof.punycode.PunySpec.out_buf Ews q n (vb ob) tk0 * TT.
Proof.
  intros Hq. unfold atok, adat.
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  rewrite !if_false by auto.
  rewrite (data_at_tuchar_cs CCS OpensslPunycode.proof.punycode.PunySpec.CS).
  destruct (Z.eq_dec n 0) as [-> | N].
  - rewrite (@malloc_token_change_composite CCS OpensslPunycode.proof.shim.ShimSpec.CS
               (CCE_any CCS OpensslPunycode.proof.shim.ShimSpec.CS) Ews (tarray tuchar 0)) by reflexivity.
    unfold tk0. cancel.
  - cancel.
Qed.

Lemma data_at_tint_csB (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma piece0 : piece9_stmt -> piece0_stmt.
Proof.
  intros H9 Espec gv. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 1).
  Intros len.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [pin bs0]. simpl fst in *. simpl snd in *. Intros.
  forward_call. Intros biglen.
  forward_call (biglen, gv).
  Intros vret. destruct vret as [pbig bb]. simpl fst in *. simpl snd in *. Intros.
  forward_call. Intros outlen.
  forward_call (outlen, gv).
  Intros vret. destruct vret as [pout ob]. simpl fst in *. simpl snd in *. Intros.
  sep_apply (@asplit CCS (len + 1) (vb bs0) pin). Intros.
  sep_apply (@asplit CCS biglen (vb bb) pbig). Intros.
  sep_apply (@asplit CCS outlen (vb ob) pout). Intros.
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pbig nullval then 1 else 0)))).
  { apply derives_trans with (@atok CCS (len + 1) pin * @adat CCS (len + 1) (vb bs0) pin * TT);
      [ cancel | apply ablock_tc; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@atok CCS biglen pbig * @adat CCS biglen (vb bb) pbig * TT);
        [ cancel | apply ablock_tc; lia ]. }
    entailer!. destruct (Val.eq pin nullval); [ contradiction | ].
    destruct (Val.eq pbig nullval); [ subst; reflexivity | ].
    nonnull_cmp pbig. }
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pbig nullval then 1 else
    if Val.eq pout nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ reflexivity | ]. destruct (Val.eq pbig nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower.
      apply derives_trans with (@atok CCS outlen pout * @adat CCS outlen (vb ob) pout * TT);
        [ cancel | apply ablock_tc; lia ]. }
    entailer!. destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pbig nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ subst; reflexivity | ].
    nonnull_cmp pout. }
  forward_if (temp _t'9 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pbig nullval then 1 else
    if Val.eq pout nullval then 1 else if Z.eq_dec outlen 0 then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ reflexivity | ]. destruct (Val.eq pbig nullval); [ reflexivity | ].
    destruct (Val.eq pout nullval); [ reflexivity | ]. contradiction. }
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pbig nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    unfold Int64.cmpu, Int64.eq. rewrite Int64.unsigned_repr by rep_lia.
    destruct (Z.eq_dec (Zlength ob) 0) as [E | E]; [ rewrite E; reflexivity | ].
    rewrite zeq_false by (change (Int64.unsigned (Int64.repr 0)) with 0; auto). reflexivity. }
  forward_if (PROP (pin <> nullval; pbig <> nullval; pout <> nullval; outlen <> 0)
    LOCAL (temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig;
           temp _biglen (Vlong (Int64.repr biglen)); temp _in pin; temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (@atok CCS outlen pout; @adat CCS outlen (vb ob) pout; @atok CCS biglen pbig;
         @adat CCS biglen (vb bb) pbig; @atok CCS (len + 1) pin; @adat CCS (len + 1) (vb bs0) pin; mem_mgr gv;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
         OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pbig nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Z.eq_dec (Zlength ob) 0); [ discriminate | auto ]. }
  Intros.
  unfold atok at 3. unfold adat at 3. rewrite !if_false by auto.
  rewrite (data_at_tuchar_cs CCS CS).
  (* in[len] = 0 *)
  forward.
  set (bs := sublist 0 len bs0).
  replace (upd_Znth len (vb bs0) (Vint (Int.zero_ext 8 (Int.repr 0)))) with (vb (bs ++ [0])).
  2: { change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). subst bs. unfold vb. list_solve. }
  (* ossl_shim_zalloc_failed = 0 *)
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite (data_at_tint_csB OpensslPunycode.proof.shim.ShimSpec.CS CS Ews (Vint (Int.repr 0))
             (gv shim.code._ossl_shim_zalloc_failed)).
  Intros.
  forward.
  sep_apply (aout_buf pbig biglen bb H10). Intros.
  sep_apply (aout_buf pout outlen ob H11). Intros.
  eapply semax_pre; [ | apply (H9 Espec gv len bs pin biglen pbig bb outlen pout ob) ].
  unfold pre9, OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite (data_at_tint_csB CS OpensslPunycode.proof.shim.ShimSpec.CS Ews (Vint (Int.repr 0))
             (gv shim.code._ossl_shim_zalloc_failed)).
  assert (Zlength bs = len) by (subst bs; list_solve).
  assert (bytes_ok bs) by (subst bs; apply Forall_sublist; auto).
  entailer!.
Qed.
