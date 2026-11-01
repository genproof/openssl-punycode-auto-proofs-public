(* Piece 5 of the main of harness/x_a2ulabel.c: the test of the three mallocs (MainDefs). *)
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

(* The value of (p == NULL) for a non-null pointer-or-null p. *)
Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece5 {Espec: OracleKind} gv v_k n pin psnap pcps:
  semax Delta_main (pre6 gv v_k n pin psnap pcps) (Ssequence T6 ret0) main_post ->
  0 <= n < Int64.max_unsigned ->
  semax Delta_main (pre5 gv v_k n pin psnap pcps) (Ssequence T5 ret0) main_post.
Proof.
  intros H6 Hn. unfold pre5, mres, T5, ret0, main_post, Delta_main. abbreviate_semax.
  forward_if (temp _t'5 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq psnap nullval then 1 else 0)))).
  { destruct (eq_dec pin nullval); [ subst; entailer! | entailer! ]. }
  { forward. entailer!. }
  { forward.
    { destruct (eq_dec psnap nullval); [ subst; entailer! | entailer! ]. }
    entailer!. destruct (Val.eq pin nullval); [ contradiction | ].
    destruct (Val.eq psnap nullval); [ subst; reflexivity | ].
    nonnull_cmp psnap. }
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pin nullval then 1 else if Val.eq psnap nullval then 1
    else if Val.eq pcps nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pin nullval); [ reflexivity | ]. destruct (Val.eq psnap nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { destruct (eq_dec pcps nullval); [ subst; entailer! | entailer! ]. }
    entailer!.
    destruct (Val.eq pin nullval); [ discriminate | ]. destruct (Val.eq psnap nullval); [ discriminate | ].
    destruct (Val.eq pcps nullval); [ subst; reflexivity | ].
    nonnull_cmp pcps. }
  forward_if (pre6 gv v_k n pin psnap pcps).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. unfold pre6. 
    destruct (Val.eq pin nullval); [ discriminate | ]. destruct (Val.eq psnap nullval); [ discriminate | ].
    destruct (Val.eq pcps nullval); [ discriminate | ].
    rewrite !if_false by auto. entailer!. }
  apply H6.
Qed.
