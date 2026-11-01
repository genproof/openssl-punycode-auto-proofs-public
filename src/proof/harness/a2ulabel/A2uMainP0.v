(* Piece 0 of the main of harness/x_a2ulabel.c: n and the three mallocs (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.

Lemma piece0 {Espec: OracleKind} gv v_k:
  (forall n pin psnap pcps, 0 <= n < Int64.max_unsigned ->
     semax Delta_main (pre5 gv v_k n pin psnap pcps) (Ssequence T5 ret0) main_post) ->
  semax Delta_main (pre0 gv v_k) (Ssequence T0 ret0) main_post.
Proof.
  intros H5. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call. Intros n.
  forward_call. Intros.
  assert (Hn: n < Int64.max_unsigned).
  { match goal with H: Int.repr (Z.b2z (Int64.ltu _ _)) <> Int.zero |- _ => revert H end.
    change (Int.signed (Int.neg (Int.repr 1))) with (-1).
    unfold Int64.ltu. rewrite (Int64.unsigned_repr n) by rep_lia.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
    destruct (zlt n Int64.max_unsigned); [ intros _; lia | intro X; contradiction X; reflexivity ]. }
  forward_call (tarray tuchar (n + 1), gv).
  { simpl; rep_lia. }
  Intros pin.
  forward_call (tarray tuchar (n + 1), gv).
  { simpl; rep_lia. }
  Intros psnap.
  forward_call (tarray tuint 512, gv).
  { simpl; rep_lia. }
  Intros pcps.
  apply (H5 n pin psnap pcps). lia.
Qed.
