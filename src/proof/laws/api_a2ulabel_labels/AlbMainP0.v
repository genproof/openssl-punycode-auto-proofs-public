(* Piece 0 of the main of harness/api_a2ulabel_labels.c: len1, len2, s1, s2, name, outlen1, outlen2, out1, out2,
   out (the ten draws), then the NULL test and the test of the two sizes against 0 (AlbP0Null.v, AlbP0Size.v, from
   the cut of AlbP0Lib.v). *)
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
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbP0Lib.
Require OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbP0Null.
Require OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbP0Size.
Local Open Scope logic.

(* After a call, VST's forward_call removes the assigned temporary from the LOCAL list by a reduction that is very
   slow here (it never ends in this main after the second upto); none of main's calls assigns a temporary already in
   that list, so the removal is the identity, checked by conversion.  The general reduction remains the fallback. *)
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    first [ change (remove_localdef_temp i L) with L
          | let u := constr:(remove_localdef_temp i L) in
            let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
            let u' := eval simpl rlt_ident_eq in u' in
            let u' := eval lazy beta iota in u' in
            let u' := eval lazy zeta in u' in
            change u with u' ]
  end.

Lemma piece0 : piece12_stmt -> piece0_stmt.
Proof.
  intros H12 Espec gv. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 2).
  Intros len1.
  forward_call (Int64.max_signed - 2 - len1).
  Intros len2.
  forward_call (len1 + 1, gv).
  Intros vr. destruct vr as [ps1 bs1]. simpl fst in *; simpl snd in *.
  fold (ablk (len1 + 1) (vb bs1) ps1).
  forward_call (len2 + 1, gv).
  Intros vr. destruct vr as [ps2 bs2]. simpl fst in *; simpl snd in *.
  fold (ablk (len2 + 1) (vb bs2) ps2).
  forward_call (tarray tuchar (len1 + len2 + 2), gv).
  { simpl. rep_lia. }
  Intros pn. fold (nblk (len1 + len2 + 2) pn).
  forward_call (Int64.max_signed).
  Intros outlen1.
  forward_call (Int64.max_signed - outlen1).
  Intros outlen2.
  forward_call (outlen1, gv).
  Intros vr. destruct vr as [po1 ob1]. simpl fst in *; simpl snd in *.
  fold (ablk outlen1 (vb ob1) po1).
  forward_call (outlen2, gv).
  Intros vr. destruct vr as [po2 ob2]. simpl fst in *; simpl snd in *.
  fold (ablk outlen2 (vb ob2) po2).
  forward_call (outlen1 + outlen2, gv).
  Intros vr. destruct vr as [po ob]. simpl fst in *; simpl snd in *.
  fold (ablk (outlen1 + outlen2) (vb ob) po).
  eapply semax_pre;
    [ | apply (AlbP0Null.alb_p0_null (AlbP0Size.alb_p0_size H12) Espec gv len1 len2 bs1 bs2 outlen1 outlen2
                 ob1 ob2 ob ps1 ps2 pn po1 po2 po) ].
  unfold pre10. entailer!.
Qed.
