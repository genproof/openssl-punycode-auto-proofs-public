(* Piece 20 of the main of harness/x_a2ulabel.c: the check of r (MainDefs). *)
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

Lemma data_at_tint_cs20 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma piece20 {Espec: OracleKind} gv v_k n bs sl pin psnap pcps outlen out want ob fn mf:
  semax Delta_main (pre20e gv v_k n bs sl pin psnap pcps outlen out want ob) S20else
    (overridePost (join21 gv v_k n bs pin psnap outlen out want) main_post) ->
  (forall l fn' zf, semax Delta_main (pre21 gv v_k n bs pin psnap outlen out want l fn' zf)
     (Ssequence T21 ret0) main_post) ->
  semax Delta_main (pre20 gv v_k n bs sl pin psnap pcps outlen out want ob fn mf) (Ssequence T20 ret0) main_post.
Proof.
  intros H20e H21. unfold pre20, T20, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. subst outlen.
  (* The outcome of the call, and what the checks need from it. *)
  remember (outcome n bs sl (Zlength ob) out ob fn mf) as oc eqn:Hoc.
  destruct oc as [[[r fn'] zf'] ov]. simpl fst; simpl snd.
  assert (Hzf: zf' = 0 \/ zf' = 1).
  { unfold outcome, OpensslPunycode.proof.punycode.PunySpec.a2u_outcome in Hoc.
    destruct (Val.eq out nullval); [ inversion Hoc; auto | ].
    destruct (Zlength ob =? 0); [ inversion Hoc; auto | ].
    destruct (negb (fn =? 0)); [ inversion Hoc; auto | ].
    destruct mf; [ inversion Hoc; auto | ].
    destruct (a2ulabel (sublist 0 sl bs) (Zlength ob)); inversion Hoc; auto. }
  assert (F1: out = nullval \/ Zlength ob = 0 \/ zf' <> 0 -> r = -1 /\ ov = vb ob).
  { unfold outcome, OpensslPunycode.proof.punycode.PunySpec.a2u_outcome in Hoc. intros C.
    destruct (Val.eq out nullval); [ inversion Hoc; auto | ].
    destruct (Zlength ob =? 0) eqn:E0; [ inversion Hoc; auto | ].
    destruct (negb (fn =? 0)); [ inversion Hoc; auto | ].
    destruct mf; [ inversion Hoc; auto | ].
    destruct (a2ulabel (sublist 0 sl bs) (Zlength ob)); inversion Hoc; subst.
    apply Z.eqb_neq in E0. destruct C as [C | [C | C]]; [ contradiction | lia | lia ]. }
  assert (F2: out <> nullval -> Zlength ob <> 0 -> zf' = 0 ->
     fn' = 0 /\ r = fst (a2ulabel (sublist 0 sl bs) (Zlength ob)) /\
     ov = vb (snd (a2ulabel (sublist 0 sl bs) (Zlength ob))) ++
          sublist (Zlength (snd (a2ulabel (sublist 0 sl bs) (Zlength ob)))) (Zlength ob) (vb ob)).
  { unfold outcome, OpensslPunycode.proof.punycode.PunySpec.a2u_outcome in Hoc. intros C1 C2 C3.
    destruct (Val.eq out nullval); [ contradiction | ].
    destruct (Zlength ob =? 0) eqn:E0; [ apply Z.eqb_eq in E0; contradiction | ].
    destruct (negb (fn =? 0)); [ inversion Hoc; lia | ].
    destruct mf; [ inversion Hoc; lia | ].
    destruct (a2ulabel (sublist 0 sl bs) (Zlength ob)); inversion Hoc; subst; auto. }
  clear Hoc.
  forward_if (temp _t'14 (Vint (Int.repr (if Val.eq out nullval then 1 else if Zlength ob =? 0 then 1 else 0)))).
  { unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
    destruct (Val.eq out nullval); [ subst; entailer! | ].
    destruct (Z.eq_dec (Zlength ob) 0); entailer!. }
  { forward. entailer!. }
  { forward. entailer!.
    rewrite if_false by auto. unfold Int64.cmpu.
    destruct (Z.eq_dec (Zlength ob) 0) as [E|E]; [ rewrite E; reflexivity | ].
    rewrite Int64.eq_false; [ rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity | ].
    intro X; apply E; apply repr_inj_unsigned64 in X; rep_lia. }
  forward_if (temp _t'15 (Vint (Int.repr (if Val.eq out nullval then 1 else if Zlength ob =? 0 then 1
                                          else if zf' =? 0 then 0 else 1)))).
  { forward. entailer!.
    destruct (Val.eq out nullval); [ reflexivity | ].
    destruct (Zlength ob =? 0); [ reflexivity | contradiction ]. }
  { unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(data_at_tint_cs20 OpensslPunycode.proof.shim.ShimSpec.CS CS). Intros.
    forward. forward. entailer!.
    { destruct (Val.eq out nullval); [ discriminate | ].
      destruct (Zlength ob =? 0); [ discriminate | ].
      destruct Hzf as [-> | ->]; reflexivity. }
    unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(data_at_tint_cs20 OpensslPunycode.proof.shim.ShimSpec.CS CS). cancel. }
  (* The if on t'15 by hand (forward_if would give its branches a normal_ret_assert post). *)
  apply semax_seq with (Q := join21 gv v_k n bs pin psnap (Zlength ob) out want).
  2: { unfold join21. Intros l fn2 zf2.
       subst MORE_COMMANDS POSTCONDITION Delta Delta_specs. unfold abbreviate. apply H21. }
  eapply semax_pre; [ | eapply semax_ifthenelse_PQR' with
    (v := Vint (Int.repr (if Val.eq out nullval then 1 else if Zlength ob =? 0 then 1
                          else if zf' =? 0 then 0 else 1))) ].
  { apply andp_left2, now_later. }
  { reflexivity. }
  { entailer!. }
  { entailer!. }
  { Intros.
    assert (C: out = nullval \/ Zlength ob = 0 \/ zf' <> 0).
    { destruct (Val.eq out nullval); auto.
      destruct (Zlength ob =? 0) eqn:E; [ apply Z.eqb_eq in E; auto | ].
      destruct (zf' =? 0) eqn:E'; [ contradiction | ]. apply Z.eqb_neq in E'; auto. }
    destruct (F1 C) as [-> ->].
    forward_call.
    unfold join21. Exists ob fn' zf'. unfold pre21. entailer!. }
  { Intros.
    assert (C: out <> nullval /\ Zlength ob <> 0 /\ zf' = 0).
    { match goal with X: Int.repr _ = Int.zero |- _ => revert X end.
      destruct (Val.eq out nullval);
        [ intro X; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate | ].
      destruct (Zlength ob =? 0) eqn:E;
        [ intro X; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate | ].
      apply Z.eqb_neq in E.
      destruct Hzf as [-> | ->];
        [ auto | intro X; apply (f_equal Int.unsigned) in X; vm_compute in X; discriminate ]. }
    destruct C as (Cn & Cl & Cz). destruct (F2 Cn Cl Cz) as (-> & -> & ->). subst zf'.
    eapply semax_pre with (P' := pre20e gv v_k n bs sl pin psnap pcps (Zlength ob) out want ob).
    { unfold pre20e, OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok,
        want_buf, arr0.
      rewrite !if_false by auto.
      rewrite (data_at_tuchar_cs OpensslPunycode.proof.punycode.PunySpec.CS CS).
      entailer!. }
    subst POSTCONDITION Delta Delta_specs. unfold abbreviate. exact H20e. }
Qed.
