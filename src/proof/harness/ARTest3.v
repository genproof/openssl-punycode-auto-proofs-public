(* pr_a2ulabel, the ACE-prefix test, 4 <= m: the test of t'3 (the first octet, x or X). *)
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

Lemma test_piece_3: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  4 <= lab_end s st - st ->
  semax Delta_a2u (lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) s_t3
    (overridePost (test_at shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv _t'3 (Val.of_bool (ace1 s st))) R).
Proof.
  intros R CTX IT GE. destruct R.
  destruct CTX as (RS & WK & WB & WC & BS & LS & CAP & LI & PS).
  destruct IT as (ST & SK & LCV & EQ).
  pose proof (lab_end_range s st ST) as LE.
  assert (V: forall i, 0 <= i < Zlength s -> @Znth val Vundef i (vb s) = Vint (Int.repr (Znth i s)))
    by (intros; apply vb_Znth; lia).
  pose proof (bytes_Znth s st BS ltac:(lia)) as C0. pose proof (bytes_Znth s (st + 1) BS ltac:(lia)) as C1.
  pose proof (bytes_Znth s (st + 2) BS ltac:(lia)) as C2. pose proof (bytes_Znth s (st + 3) BS ltac:(lia)) as C3.
  unfold lab_pre, test_at, ace1. rewrite arr0_ne by lia.
  cbv beta iota delta [s_t3 s_test]. abbreviate_semax.
  forward_if.
  - forward. { tcv V. } rewrite V by lia. forward_if.
    + forward. entailer!. fin.
    + forward. { tcv V. } rewrite V by lia. forward. forward. entailer!. fin.
  - exfalso. rewrite !Int64.unsigned_repr in H by rep_lia. lia.
Qed.

End Piece.
