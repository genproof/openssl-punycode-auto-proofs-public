(* encode: the pass over the code points for the code point n of a round (the loop over j__2). *)
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
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncPassLt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncPassDefs.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncPassLt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncPassGe.
Local Open Scope logic.

(* The loop over j__2 keeps tpass_st: each iteration is one of the two cases c < n (TrtEncPassLt.v) and n <= c
   (TrtEncPassGe.v, where c == n runs the digits of delta, given by tdig_ok). *)
Lemma tenc_pass: tdig_ok -> tpass_ok.
Proof.
  intros Hdig. unfold tpass_ok. intros. rewrite tstmt_passloop_eq. unfold tpost. abbreviate_semax.
  forward_for_simple_bound (Zlength cps) (EX j: Z, EX delta': Z, EX bias': Z, EX h: Z, EX out': list Z,
      PROP (encode cps = kont cps f n (sublist j (Zlength cps) cps) delta' bias' h B out';
            (h = h0 + cnt_eq n (sublist 0 j cps))%Z; 0 <= delta' <= maxint; 0 <= bias' <= 2400;
            Zlength out' <= room)
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta'));
         temp _bias (Vlong (Int64.repr bias')); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out' room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out'))) pl)).
  { Exists delta bias h0 out. entailer!. rewrite sublist_same by lia.
    first [exact H9 | split; [exact H9 | rewrite sublist_nil; unfold cnt_eq; simpl; rewrite Zlength_nil; lia]]. }
  { rename i into j. cbv beta. Intros delta' bias' h out'.
    assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H2; apply H2; apply Znth_In; lia).
    destruct (Z.lt_ge_cases (Znth j cps) n) as [Hlt|Hge].
    - eapply semax_pre; [ | eapply semax_post; [ | | | | eapply (tenc_pass_lt shc pc cps sho po room oinit shl pl
        f n h0 B j delta' bias' h out') ] ].
      { entailer!. }
      { rewrite HoP. unfold tpass_st. Intros d b h' o'. Exists d b h' o'. entailer!. }
      { apply brk_post. }
      { apply cont_post. }
      { intros. apply ENTAIL_refl. }
      all: auto; lia.
    - eapply semax_pre; [ | eapply semax_post; [ | | | | eapply (tenc_pass_ge shc pc cps sho po room oinit shl pl
        f n h0 B j delta' bias' h out' Hdig) ] ].
      { entailer!. }
      { rewrite HoP. unfold tpass_st. Intros d b h' o'. Exists d b h' o'. entailer!. }
      { apply brk_post. }
      { apply cont_post. }
      { intros. apply ENTAIL_refl. }
      all: auto; lia. }
  Intros delta' bias' h out'. Exists delta' bias' h out'. entailer!.
  rewrite sublist_nil, sublist_same in * by lia. split; auto.
Qed.
