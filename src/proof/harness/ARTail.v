(* pr_a2ulabel: after the label loop: write the NUL, return 0 when the sink is short, else 1. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

Lemma tail_nul: forall p, data_at Tsh tuchar (Vint (Int.repr 0)) p = arr0 Tsh tuchar 1 (vb [0]) p.
Proof.
  intros. unfold arr0. simpl. erewrite <- data_at_singleton_array_eq; reflexivity.
Qed.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val).

Lemma tail_piece:
  ar_ctx shs ps s shk cap init shb shc ->
  semax Delta_a2u (ar_brk shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u) s_tail
    (ar_post shs ps s shk pk buf cap init shb shc pc).
Proof.
  intros C; destruct C as (Rs & Wk & Wb & Wc & Bs & Ls & Lc & Li & Pp).
  intros; unfold ar_brk, ar_post; abbreviate_semax.
  Intros k cv. rename H into K. rename H0 into LCV. rename H1 into EA.
  rewrite tail_nul.
  destruct K as [LK BK].
  assert (EQ: a2ulabel s cap = (if snd (put cap k [0]) then 0 else 1, fst (put cap k [0]))).
  { rewrite a2ulabel_eq. fold (A0 s cap). rewrite EA. reflexivity. }
  unfold s_tail. forward_call (shk, pk, buf, cap, k, init, shb, Tsh, v_nul, [0]).
  { unfold bytes_ok. repeat constructor; rep_lia. }
  destruct (put cap k [0]) as [w sh] eqn:PK. simpl fst in *. simpl snd in *.
  unfold sink_rep. simpl fst. simpl snd.
  forward.
  forward_if.
  - destruct sh; [|simpl in *; contradiction].
    forward. Exists true cv. rewrite EQ, <- tail_nul. simpl. entailer!.
  - destruct sh; [inv H|].
    forward. Exists false cv. rewrite EQ, <- tail_nul. simpl. entailer!.
Qed.

End Piece.
