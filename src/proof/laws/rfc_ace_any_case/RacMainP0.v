(* Piece 0 of the main of harness/rfc_ace_any_case.c: len, any_case, outlen, out1, out2 and their NULL test
   (RacMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.rfc_ace_any_case.code.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacModel.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacLib.
Local Open Scope logic.

Module H := OpensslPunycode.proof.laws.common.HelperSpec.

(* A block from any_bytes or copy_of: NULL, or its malloc token and its octets.  Kept folded in the main: VST's
   automation is slow on the conditional of the unfolded form. *)
Definition rblk (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else @malloc_token H.CS Ews (tarray tuchar n) p * @data_at H.CS Ews (tarray tuchar n) v p.

(* The test p == NULL of such a block is defined. *)
Lemma rblk_tc_test n v p P: 0 <= n ->
  rblk n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold rblk. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - sep_apply (@data_at_data_at_ H.CS Ews (tarray tuchar n) v p).
    eapply derives_trans; [ | apply (@CmnLib.cmn_malloc_tc_test0 H.CS (tarray tuchar n) p P) ].
    + rewrite if_false by auto. cancel.
    + simpl. rep_lia.
Qed.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece0 : piece6_stmt -> piece0_stmt.
Proof.
  intros H6 Espec gv. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 5).
  Intros len.
  forward_call (len + 5, gv).
  Intros vr. destruct vr as [pa bs]. simpl fst in *; simpl snd in *.
  fold (rblk (len + 5) (vb bs) pa).
  forward_call. Intros outlen.
  forward_call (outlen, gv).
  Intros vr. destruct vr as [po1 ob]. simpl fst in *; simpl snd in *. subst outlen.
  forward_call (Ews, po1, ob, (Zlength ob), gv).
  Intros po2.
  rewrite sublist_same by lia.
  fold (rblk (Zlength ob) (vb ob) po1). fold (rblk (Zlength ob) (vb ob) po2).
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pa nullval then 1 else if Val.eq po1 nullval then 1 else 0)))).
  { apply derives_trans with (rblk (len + 5) (vb bs) pa * TT)%logic;
      [ cancel | apply rblk_tc_test; lia ]. }
  { forward. entailer!. }
  { forward.
    { go_lower. apply derives_trans with (rblk (Zlength ob) (vb ob) po1 * TT)%logic;
        [ cancel | apply rblk_tc_test; lia ]. }
    entailer!. destruct (Val.eq pa nullval); [ contradiction | ].
    destruct (Val.eq po1 nullval); [ subst; reflexivity | ].
    nonnull_cmp po1. }
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pa nullval then 1 else if Val.eq po1 nullval then 1 else
    if Val.eq po2 nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pa nullval); [ reflexivity | ]. destruct (Val.eq po1 nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower. apply derives_trans with (rblk (Zlength ob) (vb ob) po2 * TT)%logic;
        [ cancel | apply rblk_tc_test; lia ]. }
    entailer!. destruct (Val.eq pa nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ subst; reflexivity | ].
    nonnull_cmp po2. }
  forward_if (PROP (pa <> nullval; po1 <> nullval; po2 <> nullval)
    LOCAL (temp _out2 po2; temp _out1 po1; temp _outlen (Vlong (Int64.repr (Zlength ob))); temp _any_case pa;
           temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (rblk (len + 5) (vb bs) pa; rblk (Zlength ob) (vb ob) po1; rblk (Zlength ob) (vb ob) po2;
         PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    destruct (Val.eq pa nullval); [ discriminate | ].
    destruct (Val.eq po1 nullval); [ discriminate | ].
    destruct (Val.eq po2 nullval); [ discriminate | auto ]. }
  Intros. unfold rblk. rewrite !if_false by assumption.
  eapply semax_pre; [ | apply (H6 Espec gv len bs (Zlength ob) ob pa po1 po2) ].
  unfold pre6.
  rewrite !(data_at_tuchar_cs H.CS CS).
  entailer!.
Qed.
