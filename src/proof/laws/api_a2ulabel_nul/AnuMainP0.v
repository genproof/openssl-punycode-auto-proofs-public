(* The first piece of the main of harness/api_a2ulabel_nul.c: from the start of the body to the call of
   ossl_a2ulabel (AnuMainDefs): the input in, outlen, the buffer out of outlen octets and its copy saved, the NULL
   test of the three blocks, and the NUL of the string. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_nul.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuMainDefs.
Local Open Scope logic.

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* A block of n octets from malloc that may be NULL: its token and its contents, each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition atok {cs: compspecs} (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p.
Definition adat {cs: compspecs} (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp else data_at Ews (tarray tuchar n) v p.

Lemma split_block {cs: compspecs} n v p:
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)
  |-- atok n p * adat n v p.
Proof.
  unfold atok, adat. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | auto ].
Qed.

(* The test p == NULL of such a block is defined (the token is a valid pointer when n = 0). *)
Lemma block_tc_test {cs: compspecs} n v p P:
  0 <= n -> atok n p * adat n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold atok, adat. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray tuchar 0) p). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray tuchar n) v p);
        [ apply readable_nonidentity; auto | simpl; rewrite Z.max_r; lia | ].
      entailer!.
Qed.

(* The block out as ossl_a2ulabel's out buffer (the token of a zero-size block kept as tk0's). *)
Lemma out_buf_of_block (cs1: compspecs) q n v:
  q <> nullval ->
  @malloc_token cs1 Ews (tarray tuchar n) q * @data_at cs1 Ews (tarray tuchar n) v q
  |-- OpensslPunycode.proof.punycode.PunySpec.out_buf Ews q n v tk0 * TT.
Proof.
  intros Hq.
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  rewrite if_false by auto.
  rewrite (data_at_tuchar_cs cs1 OpensslPunycode.proof.punycode.PunySpec.CS).
  destruct (Z.eq_dec n 0) as [-> | N].
  - rewrite (@malloc_token_change_composite cs1 OpensslPunycode.proof.shim.ShimSpec.CS
               (CCE_any cs1 OpensslPunycode.proof.shim.ShimSpec.CS) Ews (tarray tuchar 0)) by reflexivity.
    unfold tk0. cancel.
  - cancel.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece0 {Espec: OracleKind} gv:
  (forall len bs pin outlen pout psaved ob,
     semax Delta_main (pre7 gv len bs pin outlen pout psaved ob) (Ssequence T7 ret0) main_post) ->
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
Proof.
  intros HK. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 1).
  Intros len.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [pin bs0]. simpl fst in *. simpl snd in *.
  Intros.
  sep_apply (@split_block CCS (len + 1) (vb bs0) pin). Intros.
  (* outlen = nondet_size(); out = any_bytes(outlen); saved = copy_of(out, outlen) *)
  forward_call. Intros outlen.
  forward_call (outlen, gv).
  Intros vret. destruct vret as [pout ob]. simpl fst in *. simpl snd in *.
  Intros. subst outlen.
  forward_call (Ews, pout, ob, Zlength ob, gv).
  Intros psaved. rewrite sublist_same by lia.
  sep_apply (@split_block CCS (Zlength ob) (vb ob) pout). Intros.
  sep_apply (@split_block CCS (Zlength ob) (vb ob) psaved). Intros.
  (* if (in == NULL || out == NULL || saved == NULL) return 0 *)
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pout nullval then 1 else 0)))).
  { apply derives_trans with (@atok CCS (len + 1) pin * @adat CCS (len + 1) (vb bs0) pin * TT);
      [ cancel | apply block_tc_test; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@atok CCS (Zlength ob) pout * @adat CCS (Zlength ob) (vb ob) pout * TT);
        [ cancel | apply block_tc_test; lia ]. }
    entailer!. destruct (Val.eq pin nullval); [ contradiction | ].
    destruct (Val.eq pout nullval); [ subst; reflexivity | ].
    nonnull_cmp pout. }
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pout nullval then 1 else
    if Val.eq psaved nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ reflexivity | ]. destruct (Val.eq pout nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower.
      apply derives_trans with (@atok CCS (Zlength ob) psaved * @adat CCS (Zlength ob) (vb ob) psaved * TT);
        [ cancel | apply block_tc_test; lia ]. }
    entailer!. destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Val.eq psaved nullval); [ subst; reflexivity | ].
    nonnull_cmp psaved. }
  forward_if (PROP (pin <> nullval; pout <> nullval; psaved <> nullval)
    LOCAL (temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr (Zlength ob))); temp _in pin;
           temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (@atok CCS (Zlength ob) psaved; @adat CCS (Zlength ob) (vb ob) psaved;
         @atok CCS (Zlength ob) pout; @adat CCS (Zlength ob) (vb ob) pout;
         @atok CCS (len + 1) pin; @adat CCS (len + 1) (vb bs0) pin;
         mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Val.eq psaved nullval); [ discriminate | auto ]. }
  Intros. unfold atok, adat. rewrite !if_false by assumption.
  rewrite (data_at_tuchar_cs CCS CS Ews (len + 1) (vb bs0) pin).
  (* in[len] = 0 *)
  forward.
  set (bs := sublist 0 len bs0).
  replace (upd_Znth len (vb bs0) (Vint (Int.zero_ext 8 (Int.repr 0)))) with (vb (bs ++ [0])).
  2: { change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). subst bs. unfold vb. list_solve. }
  sep_apply (out_buf_of_block CCS pout (Zlength ob) (vb ob)). Intros.
  eapply semax_pre; [ | apply (HK len bs pin (Zlength ob) pout psaved ob) ].
  unfold pre7. rewrite (data_at_tuchar_cs CCS CS Ews (Zlength ob) (vb ob) psaved).
  assert (Zlength bs = len) by (subst bs; list_solve).
  assert (bytes_ok bs) by (subst bs; apply Forall_sublist; auto).
  entailer!.
Qed.
