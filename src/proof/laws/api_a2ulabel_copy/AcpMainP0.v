(* The first piece of the main of harness/api_a2ulabel_copy.c (AcpMainDefs): len, the input in, outlen, out and
   its copy saved, then the test that returns when one of them is NULL or outlen is 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_copy.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainDefs.
Local Open Scope logic.

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* A block from malloc that may be NULL: its token and its contents (as arr0), each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition acp_tok {cs: compspecs} (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p.
Definition acp_arr {cs: compspecs} (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp else arr0 Ews tuchar n v p.

Lemma acp_split_block {cs: compspecs} n v p:
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)
  |-- acp_tok n p * acp_arr n v p.
Proof.
  unfold acp_tok, acp_arr. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  unfold arr0. destruct (Z.eq_dec n 0); [ subst; entailer! | cancel ].
  apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_inv; auto.
Qed.

(* The test p == NULL of such a block is defined. *)
Lemma acp_block_tc_test {cs: compspecs} n v p P:
  0 <= n ->
  acp_tok n p * acp_arr n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold acp_tok, acp_arr. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - unfold arr0. destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray tuchar 0) p). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray tuchar n) v p);
        [ apply readable_nonidentity; auto | simpl; rewrite Z.max_r by lia; lia | ].
      entailer!.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece0 {Espec: OracleKind} gv:
  (forall len bs0 pin outlen ob pout psaved,
     semax Delta_main (pre6 gv len bs0 pin outlen ob pout psaved) (Ssequence T6 ret0) main_post) ->
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
Proof.
  intros HK. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 1).
  Intros len.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [pin bs0]. simpl fst in *. simpl snd in *.
  forward_call (Int64.max_signed).
  Intros outlen.
  forward_call (outlen, gv).
  Intros vret. destruct vret as [pout ob]. simpl fst in *. simpl snd in *.
  assert (Hob: Zlength ob = outlen) by assumption.
  rewrite <- Hob.
  forward_call (Ews, pout, ob, Zlength ob, gv).
  Intros psaved.
  rewrite sublist_same by lia.
  sep_apply (@acp_split_block CCS (len + 1) (vb bs0) pin). Intros.
  sep_apply (@acp_split_block CCS (Zlength ob) (vb ob) pout). Intros.
  sep_apply (@acp_split_block CCS (Zlength ob) (vb ob) psaved). Intros.
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pout nullval then 1 else 0)))).
  { apply derives_trans with (@acp_tok CCS (len + 1) pin * @acp_arr CCS (len + 1) (vb bs0) pin * TT)%logic;
      [ cancel | apply acp_block_tc_test; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@acp_tok CCS (Zlength ob) pout * @acp_arr CCS (Zlength ob) (vb ob) pout * TT)%logic;
        [ cancel | apply acp_block_tc_test; lia ]. }
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
      apply derives_trans with (@acp_tok CCS (Zlength ob) psaved * @acp_arr CCS (Zlength ob) (vb ob) psaved * TT)%logic;
        [ cancel | apply acp_block_tc_test; lia ]. }
    entailer!. destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Val.eq psaved nullval); [ subst; reflexivity | ].
    nonnull_cmp psaved. }
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq pout nullval then 1 else
    if Val.eq psaved nullval then 1 else if Z.eq_dec (Zlength ob) 0 then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ reflexivity | ]. destruct (Val.eq pout nullval); [ reflexivity | ].
    destruct (Val.eq psaved nullval); [ reflexivity | ]. contradiction. }
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Val.eq psaved nullval); [ discriminate | ].
    unfold Int64.cmpu, Int64.eq. rewrite Int64.unsigned_repr by rep_lia.
    destruct (Z.eq_dec (Zlength ob) 0) as [E | E]; [ rewrite E; reflexivity | ].
    rewrite zeq_false by (change (Int64.unsigned (Int64.repr 0)) with 0; auto). reflexivity. }
  forward_if (PROP (pin <> nullval; pout <> nullval; psaved <> nullval; Zlength ob <> 0)
    LOCAL (temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr (Zlength ob))); temp _in pin;
           temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (@acp_tok CCS (len + 1) pin; @acp_arr CCS (len + 1) (vb bs0) pin;
         @acp_tok CCS (Zlength ob) pout; @acp_arr CCS (Zlength ob) (vb ob) pout;
         @acp_tok CCS (Zlength ob) psaved; @acp_arr CCS (Zlength ob) (vb ob) psaved;
         mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ].
    destruct (Val.eq pout nullval); [ discriminate | ].
    destruct (Val.eq psaved nullval); [ discriminate | ].
    destruct (Z.eq_dec (Zlength ob) 0); [ discriminate | auto ]. }
  Intros. unfold acp_tok, acp_arr. rewrite !if_false by assumption.
  unfold arr0. rewrite !if_false by (auto; lia).
  eapply semax_pre; [ | apply (HK len bs0 pin (Zlength ob) ob pout psaved) ].
  unfold pre6. rewrite !(data_at_tuchar_cs CCS CS).
  entailer!.
Qed.
