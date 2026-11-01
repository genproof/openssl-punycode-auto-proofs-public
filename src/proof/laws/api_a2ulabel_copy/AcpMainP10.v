(* The last piece of the main of harness/api_a2ulabel_copy.c (AcpMainDefs): the call of ossl_a2ulabel on the string
   s of in, then the checks: -1 when the allocation of its WPACKET record failed; else, when outlen > |s|, the result
   1, the string and its NUL written, the later octets of out unchanged (compared with saved); else the result 0
   (AcpModel.acp_a2ulabel). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_copy.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainDefs.

(* Scalars do not depend on the compspecs. *)
Lemma acp_tint_cs (cs1 cs2: compspecs) sh (v: val) q: @data_at cs1 sh tint v q = @data_at cs2 sh tint v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma acp_tlong_cs (cs1 cs2: compspecs) sh (v: val) q: @data_at cs1 sh tlong v q = @data_at cs2 sh tlong v q.
Proof.
  apply (f_equal (fun f => f q)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

(* The shim's globals as main sees them (its compspecs instead of the shim's: scalars do not depend on them). *)
Lemma acp_shim_state_cs gv fn zf live:
  OpensslPunycode.proof.shim.ShimSpec.shim_state gv fn zf live =
  (data_at Ews tint (Vint (Int.repr fn)) (gv OpensslPunycode.shim.code._ossl_shim_fail_next) *
   data_at Ews tint (Vint (Int.repr zf)) (gv _ossl_shim_zalloc_failed) *
   data_at Ews tlong (Vlong (Int64.repr live)) (gv OpensslPunycode.shim.code._ossl_shim_live))%logic.
Proof.
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(acp_tint_cs OpensslPunycode.proof.shim.ShimSpec.CS CS), (acp_tlong_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  reflexivity.
Qed.

(* The input array = the string s with its NUL (as ossl_a2ulabel's precondition wants it), then the rest t. *)
Lemma acp_in_split len s t pin:
  Zlength s + Zlength t = len ->
  data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin =
  (OpensslPunycode.proof.shim.ShimSpec.cstr Ews s pin *
   data_at Ews (tarray tuchar (len - Zlength s)) (vb t)
     (field_address0 (tarray tuchar (len + 1)) (SUB (Zlength s + 1)) pin))%logic.
Proof.
  intros Hlen.
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite app_assoc. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (Zlength s + 1)).
  - replace (len + 1 - (Zlength s + 1)) with (len - Zlength s) by lia. reflexivity.
  - rewrite Zlength_map, Zlength_app. list_solve.
  - rewrite Zlength_map. lia.
Qed.

(* The out buffer of outlen >= 1 octets as ossl_a2ulabel's out_buf (no token: the buffer is not empty). *)
Lemma acp_out_buf pout outlen v:
  pout <> nullval -> outlen <> 0 ->
  OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pout outlen v (tarray tuchar 0) =
  data_at Ews (tarray tuchar outlen) v pout.
Proof.
  intros Hp Ho. unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  rewrite if_false by auto. rewrite if_false by auto. apply sepcon_emp.
Qed.

Lemma acp_data_at_arr0 (cs1 cs2: compspecs) sh n v q:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v q = @arr0 cs2 sh tuchar n v q.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma acp_zero_emp {cs: compspecs} sh v q: data_at sh (tarray tuchar 0) v q |-- emp.
Proof.
  assert_PROP (field_compatible (tarray tuchar 0) nil q /\ Zlength v = 0) as Hfz by entailer!.
  destruct Hfz as [Hf Hz].
  apply field_compatible_isptr in Hf.
  rewrite data_at_zero_array_eq; auto. apply Zlength_nil_inv. auto.
Qed.

(* An array of octets l, cut at k into the two arrays bytes_eq reads: the first k octets at p, the rest at p + k. *)
Lemma acp_split_arr0 p l k:
  0 <= k <= Zlength l ->
  data_at Ews (tarray tuchar (Zlength l)) (vb l) p |--
  (@arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuchar k (vb (sublist 0 k l)) p *
   @arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuchar (Zlength l - k)
     (vb (sublist k (Zlength l) l)) (offset_val k p))%logic.
Proof.
  intros Hk.
  assert_PROP (field_compatible (tarray tuchar (Zlength l)) nil p) as Hfc by entailer!.
  replace (vb l) with (vb (sublist 0 k l) ++ vb (sublist k (Zlength l) l))
    by (rewrite <- vb_app, sublist_rejoin, sublist_same by lia; reflexivity).
  unfold vb.
  rewrite (split2_data_at_Tarray_app k) by (rewrite Zlength_map, Zlength_sublist; lia).
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * k) with k by lia.
  unfold arr0.
  destruct (Z.eq_dec k 0) as [e | e]; destruct (Z.eq_dec (Zlength l - k) 0) as [e0 | e0];
    rewrite ?e0; try subst k;
    rewrite !(data_at_tuchar_cs CS OpensslPunycode.proof.laws.common.HelperSpec.CS);
    repeat sep_apply (acp_zero_emp (cs:=OpensslPunycode.proof.laws.common.HelperSpec.CS)); cancel.
Qed.

(* The same with the lengths of the two parts as bytes_eq's precondition states them. *)
Lemma acp_split_len p l n k:
  Zlength l = n -> 0 <= k <= n ->
  data_at Ews (tarray tuchar n) (vb l) p |--
  (@arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuchar (Zlength (sublist 0 k l))
     (vb (sublist 0 k l)) p *
   @arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuchar (Zlength (sublist k n l))
     (vb (sublist k n l)) (offset_val k p))%logic.
Proof.
  intros Hn Hk. subst n. rewrite !Zlength_sublist by lia. replace (k - 0) with k by lia.
  apply acp_split_arr0. lia.
Qed.

(* The string s with its NUL, as the second array of the first bytes_eq. *)
Lemma acp_cstr_arr0 s p:
  OpensslPunycode.proof.shim.ShimSpec.cstr Ews s p =
  @arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuchar (Zlength (s ++ [0])) (vb (s ++ [0])) p.
Proof.
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  apply acp_data_at_arr0. pose proof (Zlength_nonneg s). simpl. lia.
Qed.

(* The octets of a string and its NUL. *)
Lemma acp_bytes_ok_str s: OpensslPunycode.proof.shim.ShimSpec.str_ok s -> bytes_ok (s ++ [0]).
Proof.
  intros Hs. unfold bytes_ok. rewrite Forall_app. split.
  - eapply Forall_impl; [ | exact Hs ]. simpl. intros. lia.
  - repeat constructor; rep_lia.
Qed.

Lemma piece10 {Espec: OracleKind} gv len s t pin outlen ob pout psaved:
  semax Delta_main (pre10 gv len s t pin outlen ob pout psaved) (Ssequence T10 ret0) main_post.
Proof.
  intros. unfold pre10, T10, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite acp_shim_state_cs. Intros.
  forward.
  rewrite (acp_in_split len s t pin) by auto. Intros.
  assert_PROP (isptr pout) as Hpout by entailer!.
  assert_PROP (isptr psaved) as Hps by entailer!.
  rewrite <- (acp_out_buf pout outlen (vb ob)) by (try (destruct pout; try contradiction; discriminate); lia).
  gather_SEP (data_at _ tint _ (gv OpensslPunycode.shim.code._ossl_shim_fail_next)) (data_at _ tint _ (gv _ossl_shim_zalloc_failed))
    (data_at _ tlong _ (gv OpensslPunycode.shim.code._ossl_shim_live)).
  rewrite <- acp_shim_state_cs.
  forward_call (gv, Ews, pin, s, Ews, pout, outlen, vb ob, tarray tuchar 0, 0, 0, 0).
  { split; [ right; rewrite Zlength_vb; auto | unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds; rep_lia ]. }
  Intros mf.
  assert (Hpn: pout <> nullval) by (destruct pout; try contradiction; discriminate).
  unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome.
  rewrite if_false by auto.
  replace (outlen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota beta. cbn [negb Z.eqb].
  destruct mf.
  - (* the allocation of the WPACKET record failed: -1 *)
    cbn [fst snd].
    rewrite acp_shim_state_cs. Intros.
    forward.
    forward_if (PROP () LOCAL () SEP (TT)).
    + forward_call. entailer!.
    + exfalso. apply Int.one_not_zero. auto.
    + forward. Exists (Int.repr 0). entailer!.
  - (* the record was allocated: Model.a2ulabel's result and output *)
    destruct (a2ulabel s outlen) as [r w] eqn:Ha. cbn [fst snd].
    rewrite acp_shim_state_cs. Intros.
    forward.
    forward_if (PROP () LOCAL () SEP (TT)).
    + contradiction.
    + forward_if.
      * (* the string and its NUL fit: 1, they are written, the rest of out is unchanged *)
        rewrite (acp_a2ulabel_fits s outlen H6) in Ha by lia. injection Ha as <- <-.
        rewrite acp_out_buf by (auto; lia).
        replace (vb (s ++ [0]) ++ sublist (Zlength (s ++ [0])) outlen (vb ob))
          with (vb ((s ++ [0]) ++ sublist (Zlength s + 1) outlen ob))
          by (rewrite vb_app; unfold vb; rewrite sublist_map, Zlength_app; reflexivity).
        sep_apply (acp_split_len pout ((s ++ [0]) ++ sublist (Zlength s + 1) outlen ob) outlen (Zlength s + 1));
          [ list_solve | list_solve | ].
        sep_apply (acp_split_len psaved ob outlen (Zlength s + 1)); [ list_solve | ]. Intros.
        replace (sublist 0 (Zlength s + 1) ((s ++ [0]) ++ sublist (Zlength s + 1) outlen ob)) with (s ++ [0])
          by list_solve.
        replace (sublist (Zlength s + 1) outlen ((s ++ [0]) ++ sublist (Zlength s + 1) outlen ob))
          with (sublist (Zlength s + 1) outlen ob) by list_solve.
        rewrite acp_cstr_arr0.
        (* what the checks do not read *)
        freeze FR := (OpensslPunycode.proof.punycode.PunySpec.puny_consts _)
          (OpensslPunycode.proof.punycode.PunySpec.xn_lit _) (data_at _ tint _ _) (data_at _ tint _ _)
          (data_at _ tlong _ _) (mem_mgr _) (data_at _ (tarray tuchar (len - Zlength s)) _ _)
          (arr0 _ _ (Zlength (sublist 0 (Zlength s + 1) ob)) _ _).
        forward_if (temp _t'15 (Vint Int.one)).
        -- forward_call (Ews, pout, s ++ [0], Ews, pin, s ++ [0]).
           { entailer!. rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity. }
           { pose proof (acp_bytes_ok_str s H0). rewrite Zlength_app, Zlength_cons, Zlength_nil. simpl.
             split; [ auto | split; [ auto | rep_lia ] ]. }
           destruct (list_eq_dec Z.eq_dec (s ++ [0]) (s ++ [0])) as [_ | E]; [ | congruence ].
           forward. entailer!.
        -- contradiction.
        -- forward_if (temp _t'17 (Vint Int.one)).
           ++ forward_call (Ews, offset_val (Zlength s + 1) pout, sublist (Zlength s + 1) outlen ob,
                            Ews, offset_val (Zlength s + 1) psaved, sublist (Zlength s + 1) outlen ob).
              { entailer!. rewrite Zlength_sublist by list_solve.
                replace (Zlength ob - (Zlength s + 1)) with (Zlength ob - Zlength s - 1) by lia. reflexivity. }
              { unfold bytes_ok in *. split; [ | split ]; try (apply Forall_sublist; auto).
                rewrite Zlength_sublist by list_solve. rep_lia. }
              destruct (list_eq_dec Z.eq_dec (sublist (Zlength s + 1) outlen ob)
                                              (sublist (Zlength s + 1) outlen ob)) as [_ | E]; [ | congruence ].
              forward. entailer!.
           ++ exfalso. apply Int.one_not_zero. auto.
           ++ forward_call. entailer!.
      * (* they do not fit: 0 *)
        pose proof (acp_a2ulabel_short s outlen H6 ltac:(lia) ltac:(lia)) as Hr. rewrite Ha in Hr. cbn in Hr.
        subst r. forward_call. entailer!.
    + forward. Exists (Int.repr 0). entailer!.
Qed.
