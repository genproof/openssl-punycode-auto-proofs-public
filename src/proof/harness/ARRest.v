(* pr_a2ulabel: after a label: break at the end of the string (ar_brk), else write '.' and continue at e + 1. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

Lemma rest_sep: forall p, data_at Tsh tuchar (Vint (Int.repr 46)) p = arr0 Tsh tuchar 1 (vb [46]) p.
Proof.
  intros. unfold arr0. destruct (Z.eq_dec 1 0); [lia|].
  symmetry. apply data_at_singleton_array_eq. reflexivity.
Qed.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma rest_piece:
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  semax Delta_a2u (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k) s_rest
    (ar_RB shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u).
Proof.
  intros CTX IT. unfold lab_post, ar_RB, ar_inv, ar_brk; abbreviate_semax.
  Intros k1 cv1. unfold s_rest.
  destruct IT as (R & K & CV & A).
  destruct CTX as (Hshs & Hshk & Hshb & Hshc & Bs & Ls & Hcap & Linit & Pps).
  pose proof (lab_end_range s st R) as LE.
  forward_if.
  - assert (E: lab_end s st = Zlength s).
    { pose proof (Int64.eq_spec (Int64.repr (lab_end s st)) (Int64.repr (Zlength s))) as Q.
      rewrite H2 in Q. apply repr_inj_unsigned64 in Q; rep_lia. }
    forward.
    destruct (ar_post shs ps s shk pk buf cap init shb shc pc) as [? ? ? ?]; cbv beta iota.
    Exists k1 cv1. entailer!.
    rewrite <- A, (a2u_labels_last s _ k st) by auto. rewrite H. reflexivity.
  - assert (E: lab_end s st <> Zlength s).
    { intro E. rewrite E in H2. contradiction. }
    rewrite rest_sep.
    assert (B46: bytes_ok [46]) by (unfold bytes_ok; repeat constructor; computable).
    forward_call (shk, pk, buf, cap, k1, init, shb, Tsh, v_sep, [46]).
    { destruct H0 as [L1 B1]. split; [auto|split; [auto|lia]]. }
    forward.
    Exists (lab_end s st + 1) (put cap k1 [46]) cv1. change (Zlength [46]) with 1. rewrite <- rest_sep.
    entailer!. split.
    + apply put_ok; auto.
    + rewrite <- A, (a2u_labels_next s _ k st) by lia. rewrite H. reflexivity.
Qed.

End Piece.
