(* encode: the loop of a round that finds the minimum code point >= n, starting from min = UINT64_MAX.  After it,
   min is fold_left (min_step n) cps Int64.max_unsigned (TrtEncModel.min_ge_u64 turns it into Model.min_ge). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Local Open Scope logic.

(* The minimum loop of a round, taken from the round's body (after min = UINT64_MAX). *)
Definition tstmt_min := ltac:(let x := eval cbv [tstmt_roundbody] in tstmt_roundbody in
  lazymatch x with Ssequence _ (Ssequence ?a _) => exact a end).

(* The rest of the round's body after the minimum loop: the overflow test, delta, n = min, the pass, delta++. *)
Definition tstmt_round2 := ltac:(let x := eval cbv [tstmt_roundbody] in tstmt_roundbody in
  lazymatch x with Ssequence _ (Ssequence _ ?b) => exact b end).

Lemma tstmt_roundbody_eq: tstmt_roundbody =
  Ssequence (Sset _min (Econst_long (Int64.repr (-1)) tulong)) (Ssequence tstmt_min tstmt_round2).
Proof. reflexivity. Qed.

Lemma tenc_min: forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl (n delta bias h B: Z)
  (out: list Z) R,
  readable_share shc -> Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> 4 * Zlength cps <= Int64.max_unsigned ->
  0 <= n <= maxint + 1 ->
  semax TDelta
   (PROP () LOCAL (temp _min (Vlong (Int64.repr Int64.max_unsigned));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl))
   tstmt_min
   (overridePost
     (PROP () LOCAL (temp _min (Vlong (Int64.repr (fold_left (min_step n) cps Int64.max_unsigned)));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)) R).
Proof.
  intros. destruct R. unfold tstmt_min. abbreviate_semax.
  forward_for_simple_bound (Zlength cps) (EX j: Z,
    PROP () LOCAL (temp _min (Vlong (Int64.repr (fold_left (min_step n) (sublist 0 j cps) Int64.max_unsigned)));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
  { entailer!. }
  { rename i into j.
    assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H0; apply H0; apply Znth_In; lia).
    assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
    pose proof (min_fold_props n (sublist 0 j cps) Int64.max_unsigned) as [Hacc0 [Hacc _]].
    set (acc := fold_left (min_step n) (sublist 0 j cps) Int64.max_unsigned) in *.
    set (c := Znth j cps) in *.
    rewrite (arr0_ne shc tuint) by lia.
    forward.
    { entailer!. rewrite Hv. simpl. auto. }
    rewrite Hv.
    assert (Hacc1: 0 <= acc) by (destruct Hacc0 as [E | [_ E]]; [rewrite E; rep_lia | lia]).
    assert (Hf: fold_left (min_step n) (sublist 0 (j + 1) cps) Int64.max_unsigned =
                if andb (n <=? c) (c <? acc) then c else acc)
      by (rewrite (sublist_split 0 j (j + 1)) by lia; rewrite sublist_len_1 by lia; rewrite fold_left_app; reflexivity).
    forward_if (PROP () LOCAL (temp _t'4 (Vint (Int.repr (if andb (n <=? c) (c <? acc) then 1 else 0)));
        temp _j__1 (Vlong (Int64.repr j)); temp _min (Vlong (Int64.repr acc));
        temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
        temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
        temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
        temp _room (Vlong (Int64.repr room)); temp _len pl)
      SEP (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
        data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
    { forward.
      { entailer!. rewrite Hv. simpl. auto. }
      rewrite Hv. forward. entailer!.
      fix_cmp. replace (n <=? c) with true by lia. simpl.
      try (unfold Int64.cmpu, Int64.ltu; rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia)).
      destruct (zlt c acc); [replace (c <? acc) with true by lia | replace (c <? acc) with false by lia];
      reflexivity. }
    { forward. entailer!. fix_cmp. replace (n <=? c) with false by lia. reflexivity. }
    forward_if.
    { forward.
      { entailer!. rewrite Hv. simpl. auto. }
      rewrite Hv. forward. rewrite <- (arr0_ne shc tuint) by lia. entailer!.
      rewrite Hf. destruct (andb (n <=? c) (c <? acc)); [ | contradiction].
      rewrite ?Int.unsigned_repr by rep_lia. reflexivity. }
    { forward. rewrite <- (arr0_ne shc tuint) by lia. entailer!.
      rewrite Hf. destruct (andb (n <=? c) (c <? acc)); [ discriminate | reflexivity]. } }
  rewrite sublist_same by lia. entailer!.
Qed.
