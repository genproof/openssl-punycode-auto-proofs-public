(* pr_encode: the loop "let m = the minimum code point >= n" of a round. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_min: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (n delta bias h B: Z) (out: list Z) R,
  readable_share shc -> Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= n <= maxint + 1 ->
  semax DeltaE
   (PROP () LOCAL (temp _mm (Vlong (Int64.repr (maxint + 1)));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_min
   (overridePost
     (PROP () LOCAL (temp _mm (Vlong (Int64.repr (min_ge cps n)));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl)) R).
Proof.
  intros. destruct R. unfold stmt_min. abbreviate_semax.
  forward_for_simple_bound (Zlength cps) (EX j: Z,
    PROP () LOCAL (temp _mm (Vlong (Int64.repr (fold_left (min_step n) (sublist 0 j cps) (maxint + 1)%Z)));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl)).
  { entailer!. }
  { rename i into j.
    assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H0; apply H0; apply Znth_In; lia).
    assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
    pose proof (min_fold_props n (sublist 0 j cps) (maxint + 1)) as [Hacc0 [Hacc _]].
    set (acc := fold_left (min_step n) (sublist 0 j cps) (maxint + 1)) in *.
    set (c := Znth j cps) in *.
    rewrite (arr0_ne shc tuint) by lia.
    forward.
    { entailer!. rewrite Hv. simpl. auto. }
    rewrite Hv.
    assert (Hacc1: 0 <= acc) by (destruct Hacc0 as [E | [_ E]]; unfold acc; lia).
    assert (Hf: fold_left (min_step n) (sublist 0 (j + 1) cps) (maxint + 1) =
                if andb (n <=? c) (c <? acc) then c else acc)
      by (rewrite (sublist_split 0 j (j + 1)) by lia; rewrite sublist_len_1 by lia; rewrite fold_left_app; reflexivity).
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if andb (n <=? c) (c <? acc) then 1 else 0)));
        temp _j (Vlong (Int64.repr j)); temp _mm (Vlong (Int64.repr acc));
        temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
        temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
        temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
        temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
        temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
      SEP (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
        data_at_ shl tulong pl)).
    { forward.
      { entailer!. rewrite Hv. simpl. auto. }
      rewrite Hv. forward. entailer!.
      fix_cmp. replace (n <=? c) with true by lia. simpl.
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by (unfold maxint in *; rep_lia).
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
