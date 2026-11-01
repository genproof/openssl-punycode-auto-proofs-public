(* pr_a2ulabel, the ACE-prefix test, m < 4: no octet is read, every test is false. *)
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

Lemma test_piece_short: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  lab_end s st - st < 4 ->
  semax Delta_a2u (lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) s_test
    (overridePost (test_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) R).
Proof.
  intros R CTX IT LT. destruct R.
  destruct CTX as (RS & WK & WB & WC & BS & LS & CAP & LI & PS).
  destruct IT as (ST & SK & LCV & EQ).
  pose proof (lab_end_range s st ST) as LE.
  unfold lab_pre, test_post. rewrite (is_ace_short s st) by lia.
  abbreviate_semax.
  forward_if (temp _t'3 (Vint (Int.repr 0))).
  - exfalso. rewrite !Int64.unsigned_repr in H by rep_lia. lia.
  - forward. entailer!.
  - forward_if (temp _t'4 (Vint (Int.repr 0))).
    + exfalso. contradiction.
    + forward. entailer!.
    + forward_if (temp _t'5 (Vint (Int.repr 0))).
      * exfalso. contradiction.
      * forward. entailer!.
      * forward_if.
        -- exfalso. contradiction.
        -- forward. entailer!.
Qed.

End Piece.
