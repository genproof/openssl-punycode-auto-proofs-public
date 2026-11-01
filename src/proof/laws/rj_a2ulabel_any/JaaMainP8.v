(* The second piece of the main of harness/rj_a2ulabel_any.c: from the call of ossl_a2ulabel to the end (JaaMainDefs):
   the call on the string of in (its octets up to the first NUL), then the checks of the result, of the input and of
   the shim's count of live blocks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rj_a2ulabel_any.code.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaProg.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaModel.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaMainDefs.

Lemma data_at_tlong_csJ (cs1 cs2: compspecs) sh v q: @data_at cs1 sh tlong v q = @data_at cs2 sh tlong v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The input array = the string (its octets up to the first NUL, with the NUL), then the rest. *)
Lemma in_split_first0 len bs pin:
  Zlength bs = len ->
  data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin =
  (OpensslPunycode.proof.shim.ShimSpec.cstr Ews (sublist 0 (first0 bs) bs) pin *
   data_at Ews (tarray tuchar (len - first0 bs)) (vb (sublist (first0 bs + 1) (len + 1) (bs ++ [0])))
     (field_address0 (tarray tuchar (len + 1)) (SUB (first0 bs + 1)) pin))%logic.
Proof.
  intros Hlen. pose proof (first0_range bs).
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite (first0_split bs) at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (first0 bs + 1)).
  - replace (len + 1 - (first0 bs + 1)) with (len - first0 bs) by lia.
    replace (Zlength (sublist 0 (first0 bs) bs) + 1) with (first0 bs + 1) by list_solve. subst len. reflexivity.
  - list_solve.
  - list_solve.
Qed.

Lemma data_at_arr0_nzJ (cs1 cs2: compspecs) sh n v q:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v q = @arr0 cs2 sh tuchar n v q.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma piece8 {Espec: OracleKind} gv len bs pin psaved outlen out ob:
  semax Delta_main (pre8 gv len bs pin psaved outlen out ob) (Ssequence T8 ret0) main_post.
Proof.
  intros. unfold pre8, T8, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite (in_split_first0 len bs pin) by auto. Intros.
  forward_call (gv, Ews, pin, sublist 0 (first0 bs) bs, Ews, out, outlen, vb ob, tk0, 0, 0, 0).
  { split; [ apply first0_str; auto | split ].
    - right. rewrite Zlength_vb. auto.
    - unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds. rep_lia. }
  Intros mf.
  pose proof (a2u_outcome_res out outlen (sublist 0 (first0 bs) bs) (vb ob) 0 0 mf) as Hres. simpl in Hres.
  remember (OpensslPunycode.proof.punycode.PunySpec.a2u_outcome out outlen (sublist 0 (first0 bs) bs) (vb ob) 0 0 mf)
    as oc.
  destruct oc as [[[r fn'] zf'] ov]. simpl in Hres |- *. clear Heqoc. destruct Hres as [Hr Hnull].
  (* gp_assert(r == 1 || r == 0 || r == -1) *)
  forward_if (temp _t'9 (Vint (Int.repr (if Z.eq_dec r 1 then 1 else if Z.eq_dec r 0 then 1 else 0)))).
  { forward. entailer!. }
  { forward. entailer!. destruct Hr as [-> | [-> | ->]]; try contradiction; reflexivity. }
  forward_if (temp _t'10 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { forward. entailer!. destruct Hr as [-> | [-> | ->]]; try discriminate; reflexivity. }
  forward_call.
  (* if (out == NULL || outlen == 0) gp_assert(r == -1) *)
  forward_if (temp _t'11 (Vint (Int.repr (if Val.eq out nullval then 1 else if Z.eq_dec outlen 0 then 1 else 0)))).
  { unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
    destruct (Val.eq out nullval); [ subst; entailer! | ].
    match goal with |- context [Z.eq_dec ?x 0] => destruct (Z.eq_dec x 0) end; entailer!. }
  { forward. entailer!. }
  { forward. entailer!.
    rewrite if_false by auto. unfold Int64.cmpu, Int64.eq. rewrite Int64.unsigned_repr by rep_lia.
    destruct (Z.eq_dec (Zlength ob) 0) as [E | E]; [ rewrite E; reflexivity | ].
    rewrite zeq_false by (change (Int64.unsigned (Int64.repr 0)) with 0; auto). reflexivity. }
  forward_if True.
  { forward_call.
    { assert (r = -1) by (apply Hnull; destruct (Val.eq out nullval); auto; destruct (Z.eq_dec outlen 0); auto;
        contradiction).
      subst r. discriminate. }
    entailer!. }
  { forward. entailer!. }
  Intros.
  (* gp_assert(bytes_eq(in, saved, len + 1)) *)
  gather_SEP (ShimSpec.cstr _ _ _) (data_at _ (tarray tuchar (len - first0 bs)) _ _).
  rewrite <- (in_split_first0 len bs pin) by auto.
  replace (len + 1) with (Zlength (bs ++ [0])) by (rewrite Zlength_app; list_solve).
  rewrite !(data_at_arr0_nzJ CS OpensslPunycode.proof.laws.common.HelperSpec.CS) by (rewrite Zlength_app; list_solve).
  forward_call (Ews, pin, bs ++ [0], Ews, psaved, bs ++ [0]).
  { entailer!. rewrite Zlength_app, Zlength_cons, Zlength_nil. simpl. reflexivity. }
  { split; [ | split ]; try (unfold bytes_ok; rewrite Forall_app; split; auto; repeat constructor; rep_lia).
    rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl; rep_lia. }
  forward_call.
  { match goal with E: Int.repr (if ?c then _ else _) = Int.zero |- _ =>
      destruct c; [ discriminate | contradiction ] end. }
  (* gp_assert(ossl_shim_live == 0) *)
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite (data_at_tlong_csJ OpensslPunycode.proof.shim.ShimSpec.CS CS). Intros.
  forward.
  forward_call.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
