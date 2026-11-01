(* Piece 0 of the main of harness/rj_decode_invalid.c: len, the input, cap, the array out and the NULL test
   (JdiMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiMainDefs.
Local Open Scope logic.

(* A block from malloc that may be NULL: its token and its contents (as arr0), each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition jtok {cs: compspecs} (t: type) (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p.
Definition jarr {cs: compspecs} (t: type) (n: Z) (v: list (reptype t)) (p: val) : mpred :=
  if eq_dec p nullval then emp else arr0 Ews t n v p.

Lemma split_block {cs: compspecs} t n v p:
  complete_legal_cosu_type t = true ->
  (if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p * data_at Ews (tarray t n) v p)
  |-- jtok t n p * jarr t n v p.
Proof.
  intros Ht. unfold jtok, jarr. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  unfold arr0. destruct (Z.eq_dec n 0); [ subst; entailer! | cancel ].
  apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_inv; auto.
Qed.

(* The test p == NULL of such a block is defined. *)
Lemma block_tc_test {cs: compspecs} t n v p P:
  (0 < n -> sizeof (tarray t n) > 0) -> sizeof (tarray t 0) <= 0 -> 0 <= n ->
  jtok t n p * jarr t n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht H0 Hn. unfold jtok, jarr. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - unfold arr0. destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray t 0) p). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray t n) v p); [ apply readable_nonidentity; auto | apply Ht; lia | ].
      entailer!.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece0 : piece5_stmt -> piece0_stmt.
Proof.
  intros H5 Espec gv vc. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call. Intros n.
  forward_call (n, gv).
  Intros vr. destruct vr as [pi bs]. simpl fst in *; simpl snd in *. subst n.
  sep_apply (@split_block C.CS tuchar (Zlength bs) (vb bs) pi eq_refl). Intros.
  forward_call. Intros c.
  forward_call (c, gv).
  Intros vr. destruct vr as [po init]. simpl fst in *; simpl snd in *.
  sep_apply (@split_block C.CS tuint c (vb init) po eq_refl). Intros.
  forward_if (temp _t'5 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq po nullval then 1 else 0)))).
  { apply derives_trans with (@jtok C.CS tuchar (Zlength bs) pi * @jarr C.CS tuchar (Zlength bs) (vb bs) pi * TT)%logic;
      [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@jtok C.CS tuint c po * @jarr C.CS tuint c (vb init) po * TT)%logic;
        [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pi nullval); [ contradiction | ].
    destruct (Val.eq po nullval); [ subst; reflexivity | ].
    nonnull_cmp po. }
  forward_if (PROP (pi <> nullval; po <> nullval)
    LOCAL (temp _out po; temp _cap (Vint (Int.repr c)); temp _input pi;
           temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
    SEP (@jtok C.CS tuint c po; @jarr C.CS tuint c (vb init) po;
         @jtok C.CS tuchar (Zlength bs) pi; @jarr C.CS tuchar (Zlength bs) (vb bs) pi;
         data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pi nullval); [ discriminate | ].
    destruct (Val.eq po nullval); [ discriminate | auto ]. }
  Intros. unfold jtok, jarr. rewrite !if_false by assumption.
  eapply semax_pre; [ | apply (H5 Espec gv vc bs pi init po) ].
  unfold pre5.
  rewrite (arr0_tuint_cs CS C.CS). rewrite !(arr0_tuchar_cs CS C.CS).
  entailer!.
Qed.
