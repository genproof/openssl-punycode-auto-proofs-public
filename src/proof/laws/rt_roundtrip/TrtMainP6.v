(* Piece 6 of the main of harness/rt_roundtrip.c: largest = 0 and the loop computing the largest code point
   (TrtMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainDefs.
Local Open Scope logic.

(* The running maximum of code points in [0, 2^32 - 1] stays in that range. *)
Lemma trt6_fold_range: forall l a,
  0 <= a <= Int.max_unsigned -> Forall (fun x => 0 <= x <= Int.max_unsigned) l ->
  0 <= fold_left Z.max l a <= Int.max_unsigned.
Proof.
  induction l as [ | x l IH]; intros a Ha Hl; simpl; auto.
  inversion Hl; subst. apply IH; auto. lia.
Qed.

(* One more turn of the loop: the maximum of the first j + 1 code points. *)
Lemma trt6_fold_step: forall l j,
  0 <= j < Zlength l ->
  fold_left Z.max (sublist 0 (j + 1) l) 0 = Z.max (fold_left Z.max (sublist 0 j l) 0) (Znth j l).
Proof.
  intros l j Hj.
  rewrite (sublist_split 0 j (j + 1)) by lia.
  rewrite fold_left_app, sublist_len_1 by lia. reflexivity.
Qed.

Lemma piece6 : piece8_stmt -> piece6_stmt.
Proof.
  intros H8 Espec gv vl vc cps outs e pc po pe. unfold pre6, T6, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward.
  forward_for_simple_bound (Zlength cps) (EX j: Z,
    PROP ()
    LOCAL (temp _largest (Vlong (Int64.repr (fold_left Z.max (sublist 0 j cps) 0)));
           temp _encoding pe; temp _out po; temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
           gvars gv; lvar _len tulong vl; lvar _count tuint vc)
    SEP (arr0 Ews tuint (Zlength cps) (vb cps) pc; arr0 Ews tuint (Zlength cps) (vb outs) po;
         arr0 Ews tuchar (Zlength e) (vb e) pe;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) vl; data_at_ Tsh tuint vc;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
  { entailer!. }
  { assert (Hn: Zlength cps <> 0) by lia. unfold arr0 at 1. rewrite if_false by exact Hn. forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. simpl. auto. }
    unfold vb at 1. rewrite Znth_map by lia.
    assert (Hc: 0 <= Znth i cps <= Int.max_unsigned) by (eapply Forall_Znth; eauto).
    assert (Hcur: 0 <= fold_left Z.max (sublist 0 i cps) 0 <= Int.max_unsigned)
      by (apply trt6_fold_range; [rep_lia | apply Forall_sublist; auto]).
    forward_if (temp _t'11 (Vlong (Int64.repr (Z.max (fold_left Z.max (sublist 0 i cps) 0) (Znth i cps))))).
    { rewrite Int.unsigned_repr in H6 by rep_lia.
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. auto. }
      unfold vb at 1. rewrite Znth_map by lia.
      forward. entailer!. rewrite Z.max_r by lia. reflexivity. }
    { rewrite Int.unsigned_repr in H6 by rep_lia.
      forward. entailer!. rewrite Z.max_l by lia. reflexivity. }
    forward. rewrite trt6_fold_step by lia. entailer!.
    unfold arr0. rewrite if_false by exact Hn. cancel. }
  rewrite sublist_same by lia.
  unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS; subst Delta POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (H8 Espec gv vl vc cps outs e pc po pe) ].
  unfold pre8, largest. entailer!.
Qed.
