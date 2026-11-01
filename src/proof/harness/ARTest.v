(* pr_a2ulabel: the ACE-prefix test of the current label: t'6 = is_ace (lab s st). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Require Import OpensslPunycode.proof.harness.ARTestH.
Require Import OpensslPunycode.proof.harness.ARTest3.
Require Import OpensslPunycode.proof.harness.ARTest4.
Require Import OpensslPunycode.proof.harness.ARTest5.
Require Import OpensslPunycode.proof.harness.ARTest6.
Require Import OpensslPunycode.proof.harness.ARTestS.
Local Open Scope logic.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma test_piece: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  semax Delta_a2u (lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) s_test
    (overridePost (test_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) R).
Proof.
  intros R CTX IT.
  destruct (Z_lt_dec (lab_end s st - st) 4) as [LT|GE].
  - apply test_piece_short; auto.
  - assert (GE4: 4 <= lab_end s st - st) by lia.
    rewrite s_test_split.
    eapply semax_seq; [eapply semax_seq; [eapply semax_seq|] |].
    + apply (test_piece_3 shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto.
    + apply (test_piece_4 shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto.
    + apply (test_piece_5 shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto.
    + apply (test_piece_6 shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto.
Qed.

End Piece.
