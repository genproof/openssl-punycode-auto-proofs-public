(* Piece 21 of the main of harness/x_a2ulabel.c: from if (out != NULL) to the end (MainDefs). *)
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

Lemma data_at_tlong_cs2 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma data_at_arr0_nz (cs1 cs2: compspecs) sh n v p:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v p = @arr0 cs2 sh tuchar n v p.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma out_arr0 (cs1 cs2: compspecs) sh n (v: list val) p:
  @data_at cs1 sh (tarray tuchar n) v p =
  ((if Z.eq_dec n 0 then @data_at cs1 sh (tarray tuchar n) v p else emp) * @arr0 cs2 sh tuchar n v p)%logic.
Proof.
  unfold arr0. destruct (Z.eq_dec n 0).
  - rewrite sepcon_emp. auto.
  - rewrite emp_sepcon. apply data_at_tuchar_cs.
Qed.

Lemma piece21 {Espec: OracleKind} gv v_k n bs pin psnap outlen out want l fn zf:
  semax Delta_main (pre21 gv v_k n bs pin psnap outlen out want l fn zf) (Ssequence T21 ret0) main_post.
Proof.
  intros. unfold pre21, T21, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. destruct H as [Hn [Hbs Hlen]]. subst outlen n.
  forward_if (PROP () LOCAL (temp _n (Vlong (Int64.repr (Zlength bs))); temp _in pin; temp _snap psnap; gvars gv;
                             lvar _k t_sink v_k)
    SEP (OpensslPunycode.proof.shim.ShimSpec.shim_state gv fn zf 0; data_at_ Tsh t_sink v_k;
         data_at Ews (tarray tuchar (Zlength bs + 1)) (vb (bs ++ [0])) pin;
         data_at Ews (tarray tuchar (Zlength bs + 1)) (vb (bs ++ [0])) psnap; TT)).
  { unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
    destruct (Val.eq out nullval); [ subst; entailer! | ].
    destruct (Z.eq_dec (Zlength l) 0); entailer!. }
  { unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, want_buf. rewrite !if_false by auto.
    rewrite (out_arr0 OpensslPunycode.proof.punycode.PunySpec.CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength l) (vb l) out).
    rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength l) (vb l) want).
    Intros.
    forward_call (Ews, out, l, Ews, want, l).
    forward_call.
    { match goal with E: Int.repr (if ?c then _ else _) = Int.zero |- _ =>
        destruct c; [ discriminate | contradiction ] end. }
    entailer!. }
  { forward. entailer!. }
  replace (Zlength bs + 1) with (Zlength (bs ++ [0])) by (rewrite Zlength_app; reflexivity).
  rewrite !(data_at_arr0_nz CS OpensslPunycode.proof.harness.RefRt.CS) by (rewrite Zlength_app; list_solve).
  forward_call (Ews, pin, bs ++ [0], Ews, psnap, bs ++ [0]).
  { entailer!. rewrite Zlength_app, Zlength_cons, Zlength_nil. simpl. reflexivity. }
  { split; [ | split ]; try (unfold bytes_ok; rewrite Forall_app; split; auto; repeat constructor; rep_lia).
    rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl; rep_lia. }
  forward_call.
  { match goal with E: Int.repr (if ?c then _ else _) = Int.zero |- _ =>
      destruct c; [ discriminate | contradiction ] end. }
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite (data_at_tlong_cs2 OpensslPunycode.proof.shim.ShimSpec.CS CS). Intros.
  forward.
  forward_call.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
