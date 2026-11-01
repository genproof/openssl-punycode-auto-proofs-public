(* The last piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): ossl_shim_zalloc_failed = 0, the call
   r = ossl_a2ulabel(label, out, outlen), the checks of r, out and want, return 0.  Proved from the model fact
   Ru8Model.ru8_a2ulabel, taken here as a hypothesis (ru8_a2ulabel_stmt) so that this file does not depend on how
   it is proved; Ru8MainP20.v applies it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.harness.ARDecRange.
Require OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.

Local Notation SCS := OpensslPunycode.proof.shim.ShimSpec.CS.
Local Notation PCS := OpensslPunycode.proof.punycode.PunySpec.CS.
#[local] Instance cce1 : change_composite_env PCS CS := CCE_any _ _.
#[local] Instance cce2 : change_composite_env CS PCS := CCE_any _ _.

Lemma ru8p20_tint_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma ru8p20_tlong_cs (cs1 cs2: compspecs) sh v p: @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The label buffer is the C string "xn--" ++ s that ossl_a2ulabel reads. *)
Lemma ru8p20_label_cstr len s pl:
  Zlength s = len ->
  data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl =
  OpensslPunycode.proof.shim.ShimSpec.cstr Ews (xn ++ s) pl.
Proof.
  intros Hl. unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs SCS CS). rewrite <- app_assoc.
  replace (Zlength (xn ++ s) + 1) with (len + 5) by (rewrite Zlength_app; unfold xn; simpl; list_solve).
  reflexivity.
Qed.

Lemma ru8p20_str_ok s:
  bytes_ok s -> Forall (fun c => c <> 46 /\ c <> 0) s ->
  OpensslPunycode.proof.shim.ShimSpec.str_ok (xn ++ s).
Proof.
  intros Hb Hn. unfold OpensslPunycode.proof.shim.ShimSpec.str_ok. apply Forall_app. split.
  - unfold xn. repeat constructor; rep_lia.
  - unfold bytes_ok in Hb. rewrite Forall_forall in *. intros x Hx.
    specialize (Hb x Hx). specialize (Hn x Hx). rep_lia.
Qed.

(* The output buffer of outlen >= 1 octets as ossl_a2ulabel's out_buf (no malloc(0) token). *)
Lemma ru8p20_out_buf outlen v pout:
  1 <= outlen -> pout <> nullval ->
  data_at Ews (tarray tuchar outlen) v pout =
  OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pout outlen v (tarray tuchar 0).
Proof.
  intros H1 Hn. unfold OpensslPunycode.proof.punycode.PunySpec.out_buf.
  rewrite if_false by auto. unfold OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  rewrite if_false by lia. rewrite sepcon_emp. apply data_at_tuchar_cs.
Qed.

Local Notation HCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* What ossl_a2ulabel does with a buffer of outlen >= 1 octets, no failure planned (knob 0) and the flag 0: when
   CRYPTO_zalloc fails, -1 and the flag 1; else the model. *)
Lemma ru8p20_outcome_mf pout outlen t init:
  pout <> nullval -> 1 <= outlen ->
  OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pout outlen t init 0 0 true = (-1, 0, 1, init).
Proof.
  intros Hn H1. unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome.
  destruct (Val.eq pout nullval); [ contradiction | ].
  replace (outlen =? 0) with false by lia. reflexivity.
Qed.

Lemma ru8p20_outcome_ok pout outlen t init:
  pout <> nullval -> 1 <= outlen ->
  OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pout outlen t init 0 0 false =
  (fst (a2ulabel t outlen), 0, 0,
   vb (snd (a2ulabel t outlen)) ++ sublist (Zlength (snd (a2ulabel t outlen))) outlen init).
Proof.
  intros Hn H1. unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome.
  destruct (Val.eq pout nullval); [ contradiction | ].
  replace (outlen =? 0) with false by lia. simpl. destruct (a2ulabel t outlen); reflexivity.
Qed.

(* The octets of ru8_want are octets (UTF-8 forms of decoded code points, all >= 0). *)
Lemma ru8p20_want_bytes s w: bytes_ok s -> ru8_want s = Some w -> bytes_ok w.
Proof.
  intros Hb. unfold ru8_want.
  destruct (Int.max_unsigned <=? Zlength s); [ discriminate | ].
  pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range s label_cap Hb ltac:(unfold label_cap; lia))
    as [Hr _].
  destruct (decode s label_cap) as [[|] cps]; [ | discriminate ].
  destruct (forallb _ cps); [ | discriminate ]. intros E; inversion E; subst w. clear E.
  simpl in Hr. induction cps as [| c cps IH]; simpl; [ constructor | ].
  inversion Hr; subst. apply Forall_app. split; [ apply OpensslPunycode.proof.harness.ARModel.utf8_bytes; lia | ].
  apply IH; auto.
Qed.

(* An array of n octets cut at k into the two arrays bytes_eq reads (nothing when one is empty). *)
Lemma ru8p20_split (cs1: compspecs) sh n k (v1 v2: list val) p:
  0 <= k <= n -> Zlength v1 = k -> Zlength v2 = n - k ->
  @data_at cs1 sh (tarray tuchar n) (v1 ++ v2) p |--
  @arr0 HCS sh tuchar k v1 p * @arr0 HCS sh tuchar (n - k) v2 (offset_val k p) * TT.
Proof.
  intros Hk H1 H2. assert_PROP (field_compatible (tarray tuchar n) [] p) as Hf by entailer!.
  rewrite (split2_data_at_Tarray_app k n sh tuchar v1 v2 p) by auto.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * k) with k by lia.
  unfold arr0. destruct (Z.eq_dec k 0), (Z.eq_dec (n - k) 0); rewrite ?(data_at_tuchar_cs cs1 HCS); cancel.
Qed.

(* A branch that the values of the tests rule out. *)
Ltac ru8p20_dead :=
  exfalso;
  first [ contradiction
        | lia
        | match goal with H: Int.repr _ = Int.zero |- _ => solve [ inversion H ] end ].

(* The statement of Ru8Model.ru8_a2ulabel. *)
Definition ru8_a2ulabel_stmt : Prop := forall s cap,
  Forall (fun c => 1 <= c <= 255 /\ c <> 46) s -> 1 <= cap ->
  match ru8_want s with
  | None => fst (a2ulabel (xn ++ s) cap) = -1
  | Some w =>
      if Zlength w + 1 <=? cap then a2ulabel (xn ++ s) cap = (1, w ++ [0])
      else fst (a2ulabel (xn ++ s) cap) = 0
  end.

Lemma piece20_of : ru8_a2ulabel_stmt -> piece20_stmt.
Proof.
  intros ru8_a2ulabel Espec gv vc len s pl outlen ob pout psaved pw sz wv.
  unfold pre20, T20, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(ru8p20_tint_cs SCS CS). rewrite !(ru8p20_tlong_cs SCS CS).
  Intros.
  forward.
  gather_SEP 8 9 10.
  replace_SEP 0 (OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0).
  { entailer!. unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(ru8p20_tint_cs SCS CS). rewrite !(ru8p20_tlong_cs SCS CS). cancel. }
  rewrite (ru8p20_label_cstr len s pl) by auto.
  rewrite (ru8p20_out_buf outlen (vb ob) pout) by (auto; lia).
  forward_call (gv, Ews, pl, xn ++ s, Ews, pout, outlen, vb ob, tarray tuchar 0, 0, 0, 0).
  { split; [ apply ru8p20_str_ok; auto | split ].
    - right. rewrite Zlength_vb. auto.
    - unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds. rep_lia. }
  Intros mf.
  assert (Hmod: Forall (fun c => 1 <= c <= 255 /\ c <> 46) s).
  { unfold bytes_ok in H1. rewrite Forall_forall in *. intros x Hx.
    specialize (H1 x Hx). specialize (H2 x Hx). rep_lia. }
  apply (ru8_a2ulabel s outlen) in Hmod; [ | lia ].
  destruct mf.
  { (* CRYPTO_zalloc failed: the flag is 1 and r = -1 *)
    rewrite ru8p20_outcome_mf by (auto; lia). cbn [fst snd].
    unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
    rewrite !(ru8p20_tint_cs SCS CS). rewrite !(ru8p20_tlong_cs SCS CS). Intros.
    forward.
    forward_if (PROP () LOCAL (lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
    { forward_call (Int.one). all: entailer!. }
    { ru8p20_dead. }
    forward. Exists (Int.repr 0). entailer!. }
  rewrite ru8p20_outcome_ok by (auto; lia). cbn [fst snd].
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(ru8p20_tint_cs SCS CS). rewrite !(ru8p20_tlong_cs SCS CS). Intros.
  forward.
  destruct (ru8_want s) as [w |] eqn:HW.
  2: { (* no decoding: valid = 0 and r = -1 *)
    rewrite Hmod.
    forward_if (PROP () LOCAL (lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
    { ru8p20_dead. }
    { forward_if.
      { forward_call (Int.one). all: entailer!. }
      { ru8p20_dead. } }
    forward. Exists (Int.repr 0). entailer!. }
  destruct H8 as [Hsz [Hw2048 Hwv]]. subst sz.
  pose proof (ru8p20_want_bytes s w H1 HW) as Hwb.
  destruct (Zlength w + 1 <=? outlen) eqn:HF.
  2: { (* too long: r = 0 *)
    rewrite Hmod. apply Z.leb_gt in HF.
    forward_if (PROP () LOCAL (lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
    { ru8p20_dead. }
    { forward_if.
      { ru8p20_dead. }
      { forward_if.
        { ru8p20_dead. }
        { forward_call (Int.one). all: entailer!. } } }
    forward. Exists (Int.repr 0). entailer!. }
  rewrite Hmod. apply Z.leb_le in HF. cbn [fst snd].
  (* fits: r = 1, out holds w, the NUL, then the octets of out after them *)
  rewrite <- (ru8p20_out_buf outlen _ pout) by (auto; lia).
  pose proof (Zlength_nonneg w).
  assert (Hk: Zlength (w ++ [0]) = Zlength w + 1) by list_solve.
  set (L := sublist (Zlength w + 1) outlen ob).
  assert (HL: Zlength L = outlen - Zlength (w ++ [0])) by (subst L; rewrite Hk; pose proof (Zlength_nonneg w); rewrite Zlength_sublist; lia).
  assert (E1: vb (w ++ [0]) ++ sublist (Zlength (w ++ [0])) outlen (vb ob) = vb (w ++ [0]) ++ vb L).
  { rewrite Hk. subst L. unfold vb. rewrite sublist_map. reflexivity. }
  assert (E2: vb ob = vb (sublist 0 (Zlength (w ++ [0])) ob) ++ vb L).
  { subst L. rewrite <- Hk, <- vb_app, <- sublist_split, sublist_same; auto; list_solve. }
  assert (E3: wv = vb (w ++ [0]) ++ sublist (Zlength (w ++ [0])) 2049 wv).
  { rewrite <- Hwv, Hk, <- sublist_split, sublist_same; auto; lia. }
  assert_PROP (isptr pout /\ isptr psaved) as Ip by entailer!. destruct Ip as [Ipo Ips].
  rewrite E1, E2, E3.
  sep_apply (ru8p20_split CS Ews outlen (Zlength (w ++ [0])) (vb (w ++ [0])) (vb L) pout);
    [ rewrite ?Zlength_vb; lia .. | ].
  sep_apply (ru8p20_split CS Ews outlen (Zlength (w ++ [0])) (vb (sublist 0 (Zlength (w ++ [0])) ob)) (vb L) psaved);
    [ rewrite ?Zlength_vb, ?Zlength_sublist; lia .. | ].
  sep_apply (ru8p20_split CS Ews 2049 (Zlength (w ++ [0])) (vb (w ++ [0]))
    (sublist (Zlength (w ++ [0])) 2049 wv) pw);
    [ rewrite ?Zlength_vb, ?Zlength_sublist; lia .. | ].
  rewrite <- HL. Intros.
  forward_if (PROP () LOCAL (lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
  { ru8p20_dead. }
  { forward_if.
    { ru8p20_dead. }
    { forward_if.
      2: { ru8p20_dead. }
      forward_if (PROP () LOCAL (temp _t'18 (Vint Int.one); temp _out pout; temp _saved psaved;
          temp _size (Vlong (Int64.repr (Zlength w + 1))); temp _outlen (Vlong (Int64.repr outlen));
          lvar _count tuint vc)
        SEP (@arr0 HCS Ews tuchar (Zlength L) (vb L) (offset_val (Zlength (w ++ [0])) pout);
             @arr0 HCS Ews tuchar (Zlength L) (vb L) (offset_val (Zlength (w ++ [0])) psaved);
             data_at_ Tsh tuint vc; TT)).
      { forward_call (Ews, pout, w ++ [0], Ews, pw, w ++ [0]).
        { entailer!. rewrite Hk. reflexivity. }
        { unfold bytes_ok in *. split; apply Forall_app; split; auto; repeat constructor; rep_lia. }
        destruct (list_eq_dec Z.eq_dec (w ++ [0]) (w ++ [0])) as [_ | C]; [ | contradiction ].
        forward. entailer!. }
      { ru8p20_dead. }
      forward_if (PROP () LOCAL (temp _t'20 (Vint Int.one); lvar _count tuint vc) SEP (data_at_ Tsh tuint vc; TT)).
      { forward_call (Ews, offset_val (Zlength (w ++ [0])) pout, L, Ews, offset_val (Zlength (w ++ [0])) psaved, L).
        { entailer!. rewrite Hk, HL, Hk.
          destruct pout; try contradiction. destruct psaved; try contradiction. reflexivity. }
        { subst L. unfold bytes_ok in *. split; apply Forall_sublist; auto. }
        destruct (list_eq_dec Z.eq_dec L L) as [_ | C]; [ | contradiction ].
        forward. entailer!. }
      { ru8p20_dead. }
      forward_call (Int.one). entailer!. } }
  forward. Exists (Int.repr 0). entailer!.
Qed.
