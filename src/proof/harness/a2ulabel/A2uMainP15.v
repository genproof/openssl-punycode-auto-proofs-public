(* The then-branch of if ((mode & 1) == 0) in the main of harness/x_a2ulabel.c: out and want (MainDefs). *)
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

(* QuickProof's nondet_bytes takes buf = NULL when n = 0; here buf is a pointer (isptr, or a field_compatible
   fact), so the specification's conditional pre- and postcondition are their non-NULL branch. *)
Ltac nonnull_tac := let H := fresh in intro H;
  first [ assumption
        | match goal with Hp: ?p <> nullval |- _ => rewrite H in Hp; contradiction end
        | match goal with Hp: isptr ?p |- _ => rewrite H in Hp; simpl in Hp; contradiction end
        | match goal with Hp: field_compatible _ _ ?p |- _ =>
            rewrite H in Hp; destruct Hp as [Hp _]; simpl in Hp; contradiction end ].

(* The value of (p == NULL) for a non-null pointer-or-null p. *)
Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

(* Every tuchar array at the law's compspecs. *)
Ltac to_cs :=
  repeat match goal with |- context [@data_at ?c ?sh (tarray tuchar ?k) ?v ?p] =>
    tryif constr_eq c CS then fail else rewrite (data_at_tuchar_cs c CS sh k v p) end.

Lemma piece15 {Espec: OracleKind} gv v_k n bs sl pin psnap pcps outlen m:
  semax Delta_main (pre15 gv v_k n bs sl pin psnap pcps outlen m) S15then
    (overridePost (join16 gv v_k n bs sl pin psnap pcps outlen m) main_post).
Proof.
  intros. unfold pre15, S15then, main_post, Delta_main. abbreviate_semax. Intros.
  forward_call (tarray tuchar outlen, gv).
  { simpl; rep_lia. }
  Intros out.
  forward_call (tarray tuchar outlen, gv).
  { simpl; rep_lia. }
  Intros want.
  forward_if (temp _t'11 (Vint (Int.repr (if Val.eq out nullval then 1 else if Val.eq want nullval then 1 else 0)))).
  { destruct (eq_dec out nullval); [ subst; entailer! | entailer! ]. }
  { forward. entailer!. }
  { forward.
    { destruct (eq_dec want nullval); [ subst; entailer! | entailer! ]. }
    entailer!. destruct (Val.eq out nullval); [ contradiction | ].
    destruct (Val.eq want nullval); [ subst; reflexivity | ].
    nonnull_cmp want. }
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  destruct (Val.eq out nullval); [ discriminate | ]. destruct (Val.eq want nullval); [ discriminate | ].
  rewrite !if_false by auto. Intros.
  forward_call (out, outlen, Ews).
  { rewrite if_false by nonnull_tac. cancel. }
  Intros ob. rewrite if_false by nonnull_tac.
  subst outlen. fold (vb ob). destruct (Z.eq_dec (Zlength ob) 0) as [Z0|Z0].
  - apply Zlength_nil_inv in Z0. subst ob.
    forward_call (Ews, want, @nil val, Ews, out, @nil Z).
    { unfold arr0. rewrite !if_true by reflexivity. cancel. }
    unfold join16. Exists out want (@nil Z). unfold pre16, want_buf, PunySpec.out_buf, shim.ShimSpec.zero_tok, arr0.
    change (Zlength (@nil Z)) with 0 in *.
    destruct (Z.eq_dec 0 0); [ | congruence ]. destruct (Val.eq out nullval); [ contradiction | ].
    match goal with |- context [@malloc_token ?c Ews tk0 out] =>
      rewrite (@malloc_token_change_composite c CS (CCE_any c CS) Ews tk0) by reflexivity end.
    to_cs. unfold tk0. entailer!.
  - forward_call (Ews, want, Zrepeat Vundef (Zlength ob), Ews, out, ob).
    { unfold arr0. rewrite !if_false by auto. to_cs. rewrite data_at__tarray. cancel. }
    { apply Zlength_Zrepeat; rep_lia. }
    unfold join16. Exists out want ob. unfold pre16, want_buf, PunySpec.out_buf, shim.ShimSpec.zero_tok, arr0.
    destruct (Z.eq_dec (Zlength ob) 0); [ contradiction | ]. destruct (Val.eq out nullval); [ contradiction | ].
    to_cs. entailer!.
Qed.
