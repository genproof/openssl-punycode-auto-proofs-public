(* pr_a2ulabel, the ACE-prefix test, 4 <= m: the test of t'6 (the fourth octet, a hyphen). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Require Import OpensslPunycode.proof.harness.ARTestH.
Local Open Scope logic.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma test_piece_6: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  4 <= lab_end s st - st ->
  semax Delta_a2u (test_at shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv _t'5 (Val.of_bool (ace3 s st))) s_t6
    (overridePost (test_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) R).
Proof.
  intros R CTX IT GE. destruct R.
  destruct CTX as (RS & WK & WB & WC & BS & LS & CAP & LI & PS).
  destruct IT as (ST & SK & LCV & EQ).
  pose proof (lab_end_range s st ST) as LE.
  assert (V: forall i, 0 <= i < Zlength s -> @Znth val Vundef i (vb s) = Vint (Int.repr (Znth i s)))
    by (intros; apply vb_Znth; lia).
  pose proof (bytes_Znth s st BS ltac:(lia)) as C0. pose proof (bytes_Znth s (st + 1) BS ltac:(lia)) as C1.
  pose proof (bytes_Znth s (st + 2) BS ltac:(lia)) as C2. pose proof (bytes_Znth s (st + 3) BS ltac:(lia)) as C3.
  unfold test_post, test_at. rewrite (is_ace_lab s st) by lia.
  rewrite arr0_ne by lia. unfold ace3, ace2, ace1.
  cbv beta iota delta [s_t6 s_test]. abbreviate_semax.
  forward_if.
  - forward. { tcv V. } rewrite V by lia. forward. entailer!. fin.
  - forward. entailer!. fin.
Qed.

End Piece.
