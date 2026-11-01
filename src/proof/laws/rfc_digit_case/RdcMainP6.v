(* Piece 6 of the main of harness/rfc_digit_case.c: the NULL test of input, other, out1 and out2 (RdcMainDefs); the
   state before it, with each block from malloc possibly NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcModel.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainDefs.
Local Open Scope logic.

(* A block from malloc that may be NULL: its token and its contents (as arr0), each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition rtok {cs: compspecs} (t: type) (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p.
Definition rarr {cs: compspecs} (t: type) (n: Z) (v: list (reptype t)) (p: val) : mpred :=
  if eq_dec p nullval then emp else arr0 Ews t n v p.

Lemma split_block {cs: compspecs} t n v p:
  complete_legal_cosu_type t = true ->
  (if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p * data_at Ews (tarray t n) v p)
  |-- rtok t n p * rarr t n v p.
Proof.
  intros Ht. unfold rtok, rarr. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  unfold arr0. destruct (Z.eq_dec n 0); [ subst; entailer! | cancel ].
  apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_inv; auto.
Qed.

(* The test p == NULL of such a block is defined. *)
Lemma block_tc_test {cs: compspecs} t n v p P:
  (0 < n -> sizeof (tarray t n) > 0) -> sizeof (tarray t 0) <= 0 -> 0 <= n ->
  rtok t n p * rarr t n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht H0 Hn. unfold rtok, rarr. destruct (eq_dec p nullval).
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

Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.

(* Cut 6: the four blocks from malloc (each NULL or its token and contents), before the NULL test. *)
Definition pre6 (gv: globals) (v1 v2: val) (bs: list Z) (pi ps: val) (init1: list Z) (po1: val)
    (init2: list Z) (po2: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init1 <= Int.max_unsigned;
        Zlength init2 = Zlength init1; u32s init1; u32s init2)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps;
         temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1;
         lvar _count2 tuint v2)
  SEP (@rtok C.CS tuint (Zlength init1) po2; @rarr C.CS tuint (Zlength init1) (vb init2) po2;
       @rtok C.CS tuint (Zlength init1) po1; @rarr C.CS tuint (Zlength init1) (vb init1) po1;
       @rtok C.CS tuchar (Zlength bs) ps; @rarr C.CS tuchar (Zlength bs) (vb bs) ps;
       @rtok C.CS tuchar (Zlength bs) pi; @rarr C.CS tuchar (Zlength bs) (vb bs) pi;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

Definition piece6_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs pi ps init1 po1 init2 po2,
  semax Delta_main (pre6 gv v1 v2 bs pi ps init1 po1 init2 po2) (Ssequence T6 ret0) main_post.

Lemma piece6 : piece7_stmt -> piece6_stmt.
Proof.
  intros H7 Espec gv v1 v2 bs pi ps init1 po1 init2 po2. unfold pre6, T6, ret0, main_post, Delta_main.
  abbreviate_semax. Intros.
  pose proof (Zlength_nonneg init1). pose proof (Zlength_nonneg bs). set (c := Zlength init1).
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq ps nullval then 1 else 0)))).
  { apply derives_trans with (@rtok C.CS tuchar (Zlength bs) pi * @rarr C.CS tuchar (Zlength bs) (vb bs) pi * TT)%logic;
      [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@rtok C.CS tuchar (Zlength bs) ps * @rarr C.CS tuchar (Zlength bs) (vb bs) ps * TT)%logic;
        [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pi nullval); [ contradiction | ].
    destruct (Val.eq ps nullval); [ subst; reflexivity | ].
    nonnull_cmp ps. }
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq ps nullval then 1 else
    if Val.eq po1 nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pi nullval); [ reflexivity | ]. destruct (Val.eq ps nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower.
      apply derives_trans with (@rtok C.CS tuint c po1 * @rarr C.CS tuint c (vb init1) po1 * TT)%logic;
        [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pi nullval); [ discriminate | ].
    destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ subst; reflexivity | ].
    nonnull_cmp po1. }
  forward_if (temp _t'9 (Vint (Int.repr (if Val.eq pi nullval then 1 else if Val.eq ps nullval then 1 else
    if Val.eq po1 nullval then 1 else if Val.eq po2 nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pi nullval); [ reflexivity | ]. destruct (Val.eq ps nullval); [ reflexivity | ].
    destruct (Val.eq po1 nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower.
      apply derives_trans with (@rtok C.CS tuint c po2 * @rarr C.CS tuint c (vb init2) po2 * TT)%logic;
        [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pi nullval); [ discriminate | ].
    destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ subst; reflexivity | ].
    nonnull_cmp po2. }
  forward_if (PROP (pi <> nullval; ps <> nullval; po1 <> nullval; po2 <> nullval)
    LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr c)); temp _other ps; temp _input pi;
           temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
    SEP (@rtok C.CS tuint c po2; @rarr C.CS tuint c (vb init2) po2;
         @rtok C.CS tuint c po1; @rarr C.CS tuint c (vb init1) po1;
         @rtok C.CS tuchar (Zlength bs) ps; @rarr C.CS tuchar (Zlength bs) (vb bs) ps;
         @rtok C.CS tuchar (Zlength bs) pi; @rarr C.CS tuchar (Zlength bs) (vb bs) pi;
         data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         mem_mgr gv; TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pi nullval); [ discriminate | ].
    destruct (Val.eq ps nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ discriminate | auto ]. }
  Intros. unfold rtok, rarr. rewrite !if_false by assumption.
  eapply semax_pre; [ | apply (H7 Espec gv v1 v2 bs pi ps init1 po1 init2 po2) ].
  unfold pre7, u32s in *. subst c.
  rewrite !(arr0_tuint_cs CS C.CS). rewrite !(arr0_tuchar_cs CS C.CS).
  entailer!.
Qed.
