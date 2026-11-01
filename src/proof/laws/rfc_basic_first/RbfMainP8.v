(* Piece 8 of the main of harness/rfc_basic_first.c: the loop over the literal octets, which checks r == 0 at every
   octet >= 0x80 (RbfMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.harness.rfc_basic_first.code.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfMainDefs.
Local Open Scope logic.

Lemma piece8 : piece9_stmt -> piece8_stmt.
Proof.
  intros H9 Espec gv vc bs pi cap po r a cnt. unfold pre8, T8, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  pose proof (DecModel.last_delim_range bs) as Hb. pose proof (Zlength_nonneg bs).
  assert (Hbl: last_delim bs <= Zlength bs) by lia.
  forward_for_simple_bound (last_delim bs)
    (EX i: Z, PROP ()
      LOCAL (temp _r (Vint (Int.repr r)); temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po;
             temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
      SEP (arr0 Ews tuint cap a po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
           data_at Tsh tuint (Vint (Int.repr cnt)) vc; TT)).
  - entailer!.
  - unfold arr0 at 2. rewrite if_false by lia.
    assert (Hi: 0 <= Znth i bs <= 255) by (unfold bytes_ok in H; rewrite Forall_Znth in H; apply H; lia).
    forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold vb at 1. rewrite Znth_map by lia.
    forward_if True.
    + destruct H2 as [_ [Hr _]]. assert (r = 0) by (apply (Hr i); lia). subst r.
      forward_call (Int.one). entailer!.
    + forward. entailer!.
    + entailer!. unfold arr0. rewrite if_false by lia. cancel.
  - eapply semax_pre; [ | apply (H9 Espec gv vc bs pi cap po r a cnt) ].
    unfold pre8. entailer!.
Qed.
