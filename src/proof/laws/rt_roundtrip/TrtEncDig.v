(* encode, the branch c == n of the pass: the digits of delta through put and digit, rfc_adapt, delta = 0, h++. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDigDefs.
Local Open Scope logic.

(* The loop "for (k = 36;; k += 36)" runs with the invariant tdig_inv (the digits written so far are a prefix of
   enc_digits 64 delta 36 bias, fuel f2 for k = 36 (65 - f2)); a put that fails means the encoding, if any, is longer
   than room, so encode_fits is false and the return of 0 meets tpost. *)
Lemma tenc_dig: tdig_ok.
Proof.
  unfold tdig_ok, tpost. intros. unfold tstmt_digs.
  forward. forward.
  forward_loop (tdig_inv shc pc cps sho po room oinit shl pl n delta bias h b j out)
    continue: (tdig_inc shc pc cps sho po room oinit shl pl n delta bias h b j out)
    break: (tdig_brk shc pc cps sho po room oinit shl pl n delta bias h b j out).
  { unfold tdig_inv. Exists delta 64%nat (@nil Z). rewrite app_nil_r. entailer!.
    pose proof maxint_lt_pow. lia. }
  { (* the body: the threshold t, the break on q < t, the digit of q, q = (q - t) / (36 - t) *)
    unfold tdig_inv. Intros q f2 wr.
    assert (Hk: 36 <= 36 + 36 * (64 - Z.of_nat f2) <= 36 * 65) by lia.
    forward_if (temp _t'6 (Vlong (Int64.repr (threshold (36 + 36 * (64 - Z.of_nat f2)) bias)))).
    { forward. entailer!. unfold threshold. replace (_ <=? bias) with true by lia. reflexivity. }
    { forward_if.
      { forward. forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. unfold threshold.
        replace (_ <=? bias) with false by lia. replace (bias + 26 <=? _) with true by lia. reflexivity. }
      { forward. forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. unfold threshold.
        replace (_ <=? bias) with false by lia. replace (bias + 26 <=? _) with false by lia. reflexivity. } }
    forward.
    pose proof (threshold_range (36 + 36 * (64 - Z.of_nat f2)) bias) as Ht.
    forward_if.
    { fix_ltu. forward. unfold tdig_brk. Exists q wr. entailer!.
      rewrite (enc_digits_last f2 q _ bias) in H11 by assumption. auto. }
    fix_ltu. destruct f2 as [|f3]; [simpl in H12; lia|].
    set (k := 36 + 36 * (64 - Z.of_nat (S f3))) in *.
    set (t := threshold k bias) in *.
    assert (Hm: 0 <= (q - t) mod (36 - t) < 36 - t) by (apply Z.mod_pos_bound; lia).
    forward_call (t + (q - t) mod (36 - t)).
    { rewrite Int.signed_repr in * by rep_lia. repr0_false. }
    { entailer!. simpl. rewrite modu_repr64 by (unfold maxint in *; rep_lia). rewrite add64_repr. reflexivity. }
    pose proof (digit_char_range (t + (q - t) mod (36 - t)) ltac:(lia)) as Hdc.
    forward_call (sho, po, room, bufv (out ++ wr) room oinit, shl, pl, Zlength (out ++ wr),
                  digit_char (t + (q - t) mod (36 - t))).
    { apply bufv_len; lia. }
    destruct (Zlength (out ++ wr) <? room) eqn:Er; [apply Z.ltb_lt in Er | apply Z.ltb_ge in Er].
    { forward_if. { discriminate. }
      rewrite bufv_upd by lia.
      forward.
      { entailer!. rewrite Int.signed_repr in * by rep_lia. repr0_false. }
      assert (Hq': 0 <= (q - t) / (36 - t) < 10 ^ Z.of_nat f3) by (apply digit_q_bound; auto; lia).
      rewrite (enc_digits_S f3 q k bias) in H11 by assumption.
      unfold tdig_inc. Exists ((q - t) / (36 - t)) f3 (wr ++ [digit_char (t + (q - t) mod (36 - t))]).
      entailer!.
      { assert (Hk': 36 + 36 * (64 - Z.of_nat f3) = k + 36) by (unfold k; rewrite Nat2Z.inj_succ; lia).
        rewrite Hk'. split; [rewrite H11, <- app_assoc; reflexivity|].
        split; [apply Z.div_le_upper_bound; [lia | unfold maxint in *; nia]|].
        split; [rewrite app_assoc, Zlength_app, Zlength_cons, Zlength_nil; lia|].
        split; [rewrite divu_repr64 by (unfold maxint in *; rep_lia); reflexivity|].
        do 2 f_equal. unfold k. rewrite Nat2Z.inj_succ. lia. }
      rewrite app_assoc, (Zlength_app _ (out ++ wr)), Zlength_cons, Zlength_nil. cancel. }
    (* put failed: the output is full *)
    forward_if; [ | contradiction].
    forward.
    eapply derives_trans; [ | apply (tret0_entail cps _ oinit shc pc sho po shl pl
      (bufv (out ++ wr) (Zlength oinit) oinit) (Vlong (Int64.repr (Zlength (out ++ wr))))) ];
      [cancel | | apply bufv_len; lia].
    eapply (kont_dig_fail cps f n rest _ _ _ b out wr (enc_digits (S f3) q k bias)).
    rewrite H5, H11. reflexivity. apply enc_digits_nonempty. lia. }
  { (* the increment k = k + 36 *)
    unfold tdig_inc, tdig_inv. Intros q f2 wr. forward. Exists q f2 wr. entailer!. do 2 f_equal; lia. }
  (* after the loop: the last digit q, adapt, delta = 0, h++ *)
  unfold tdig_brk. Intros q wr.
  pose proof (digit_char_range q ltac:(lia)) as Hdc.
  forward_call q.
  forward_call (sho, po, room, bufv (out ++ wr) room oinit, shl, pl, Zlength (out ++ wr), digit_char q).
  { apply bufv_len; lia. }
  destruct (Zlength (out ++ wr) <? room) eqn:Er; [apply Z.ltb_lt in Er | apply Z.ltb_ge in Er].
  2: { forward_if; [ | contradiction].
    forward.
    eapply derives_trans; [ | apply (tret0_entail cps _ oinit shc pc sho po shl pl
      (bufv (out ++ wr) (Zlength oinit) oinit) (Vlong (Int64.repr (Zlength (out ++ wr))))) ];
      [cancel | | apply bufv_len; lia].
    eapply (kont_dig_fail cps f n rest _ _ _ b out wr [digit_char q]).
    rewrite H5, H11. reflexivity. rewrite Zlength_cons, Zlength_nil. lia. lia. }
  forward_if. { discriminate. }
  rewrite bufv_upd by lia.
  forward_call (delta, h + 1, if h =? b then 1 else 0).
  { entailer!. simpl. unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq h b), (h =? b) eqn:E; try reflexivity; [apply Z.eqb_neq in E | apply Z.eqb_eq in E]; lia. }
  { destruct (h =? b); rep_lia. }
  replace (negb ((if h =? b then 1 else 0) =? 0)) with (h =? b) by (destruct (h =? b); reflexivity).
  forward. forward.
  unfold tdig_q. entailer!.
  { rewrite H11, app_assoc, (Zlength_app _ (out ++ wr)), Zlength_cons, Zlength_nil. lia. }
  rewrite H11, app_assoc, (Zlength_app _ (out ++ wr)), Zlength_cons, Zlength_nil. cancel.
Qed.
