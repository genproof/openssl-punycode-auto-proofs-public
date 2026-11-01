(* Piece 16 of the main of harness/x_a2ulabel.c: the knob, the counters and the call of ossl_a2ulabel (MainDefs). *)
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

Lemma data_at_tint_cs16 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma data_at_tlong_cs16 (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The input array = the string s = the first sl octets with its NUL, then the rest. *)
Lemma in_split n bs sl pin:
  in_ok n bs -> sl_ok n bs sl ->
  data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin =
  (OpensslPunycode.proof.shim.ShimSpec.cstr Ews (sublist 0 sl bs) pin *
   data_at Ews (tarray tuchar (n - sl)) (vb (sublist (sl + 1) (n + 1) (bs ++ [0])))
     (field_address0 (tarray tuchar (n + 1)) (SUB (sl + 1)) pin))%logic.
Proof.
  intros [Hn [Hok Hlen]] [Hsl [Hnz Hz]].
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  assert (E: bs ++ [0] = (sublist 0 sl bs ++ [0]) ++ sublist (sl + 1) (n + 1) (bs ++ [0])).
  { rewrite <- Hz. subst n. list_solve. }
  rewrite E at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (sl + 1)).
  - replace (n + 1 - (sl + 1)) with (n - sl) by lia.
    replace (Zlength (sublist 0 sl bs) + 1) with (sl + 1) by list_solve. reflexivity.
  - list_solve.
  - list_solve.
Qed.

Lemma knob_eq m: 0 <= m <= Byte.max_unsigned ->
  Z.b2z (negb (Int.eq (Int.and (Int.repr m) (Int.repr 2)) (Int.repr 0))) = knob m.
Proof.
  intros Hm. unfold Int.and, knob.
  rewrite (Int.unsigned_repr m) by rep_lia. rewrite (Int.unsigned_repr 2) by rep_lia.
  assert (E4: Z.land m 2 = Z.land m 2 mod 4).
  { change 4 with (2 ^ 2). rewrite <- (Z.land_ones _ 2) by lia. rewrite <- Z.land_assoc. reflexivity. }
  assert (0 <= Z.land m 2 < 4) by (rewrite E4; apply Z.mod_pos_bound; lia).
  unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia.
  destruct (Z.land m 2 =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. reflexivity.
  - apply Z.eqb_neq in E. rewrite zeq_false by auto. reflexivity.
Qed.

Lemma piece16 {Espec: OracleKind} gv v_k n bs sl pin psnap pcps outlen m out want ob:
  (forall fn mf, semax Delta_main (pre20 gv v_k n bs sl pin psnap pcps outlen out want ob fn mf)
     (Ssequence T20 ret0) main_post) ->
  semax Delta_main (pre16 gv v_k n bs sl pin psnap pcps outlen m out want ob) (Ssequence T16 ret0) main_post.
Proof.
  intros HK. unfold pre16, T16, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(data_at_tint_cs16 OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite !(data_at_tlong_cs16 OpensslPunycode.proof.shim.ShimSpec.CS CS).
  Intros.
  forward. forward. forward.
  rewrite (knob_eq m) by auto. change (Int.signed (Int.repr 0)) with 0.
  gather_SEP 3 4 5.
  replace_SEP 0 (OpensslPunycode.proof.shim.ShimSpec.shim_state gv (knob m) 0 0).
  { entailer!. unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(data_at_tint_cs16 OpensslPunycode.proof.shim.ShimSpec.CS CS).
    rewrite !(data_at_tlong_cs16 OpensslPunycode.proof.shim.ShimSpec.CS CS). cancel. }
  rewrite (in_split n bs sl pin) by auto. Intros.
  forward_call (gv, Ews, pin, sublist 0 sl bs, Ews, out, outlen, vb ob, tk0, knob m, 0, 0).
  { destruct H as [_ [Hok _]]. destruct H0 as [_ [Hnz _]]. split; [ | split ].
    - unfold OpensslPunycode.proof.shim.ShimSpec.str_ok. unfold bytes_ok in Hok.
      apply (Forall_sublist _ 0 sl) in Hok.
      rewrite Forall_forall in *. intros x Hx. specialize (Hok x Hx). specialize (Hnz x Hx). rep_lia.
    - right. unfold vb. rewrite Zlength_map. auto.
    - unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds, knob.
      destruct (Z.land m 2 =? 0); rep_lia. }
  Intros mf.
  eapply semax_pre; [ | apply (HK (knob m) mf) ].
  unfold pre20, outcome. rewrite (in_split n bs sl pin) by auto.
  assert (knob m = 0 \/ knob m = 1) by (unfold knob; destruct (Z.land m 2 =? 0); auto).
  entailer!.
Qed.
