(* encode: the main loop (one round per code point value >= 128 present) and the end (return 1). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Local Open Scope logic.

(* From the state after the basic code points and the delimiter (out0) to the end of encode. *)
Lemma tenc_main: tround_ok -> forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl (B: Z) (out0: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> 4 * Zlength cps <= Int64.max_unsigned ->
  0 <= room <= Int64.max_unsigned -> Zlength oinit = room ->
  B = Zlength (filter (fun c => c <? 128) cps) ->
  out0 = (if 0 <? B then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps) ->
  Zlength out0 <= room ->
  semax TDelta
   (PROP () LOCAL (temp _b (Vlong (Int64.repr B));
      temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out0 room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out0))) pl))
   (Ssequence tstmt_mainloop (Sreturn (Some (Econst_int (Int.repr 1) tint))))
   (tpost shc pc cps sho po room oinit shl pl).
Proof.
  intros Hround. intros. unfold tstmt_mainloop, tpost. abbreviate_semax.
  assert (HB: 0 <= B <= Zlength cps) by (subst B; split; [apply Zlength_nonneg | apply (cnt_lt_le 128 cps)]).
  forward.
  forward_loop (tenc_inv shc pc cps sho po room oinit shl pl B)
    continue: (tenc_cont shc pc cps sho po room oinit shl pl B)
    break: (EX out: list Z,
      PROP (encode cps = Some out; Zlength out <= room)
      LOCAL (temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
             temp _room (Vlong (Int64.repr room)); temp _len pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
           data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl)).
  { unfold tenc_inv. Exists 128 0 72 B out0 (S (length cps)).
    entailer!. rewrite Nat2Z.inj_succ, <- Zlength_correct. lia. }
  { unfold tenc_inv. Intros n delta bias h out f.
    pose proof (cnt_lt_le n cps).
    forward_if.
    { fix_cmp.
      eapply semax_post; [ | | | | apply (Hround Espec shc pc cps sho po room oinit shl pl B n delta bias h out f);
        auto; lia].
      2: apply brk_enc. 2: apply cont_enc. 2: (intros; apply ENTAIL_refl).
      unfold POSTCONDITION, abbreviate. rewrite RA_normal_oP, RA_normal_loop1. apply ENTAIL_refl. }
    { fix_cmp. destruct f as [|f]; [simpl in H10; lia|].
      rewrite enc_rounds_done in H9 by lia. forward. Exists out. entailer!. } }
  { unfold tenc_cont, tenc_inv. Intros n delta bias h out f. forward.
    Exists (n + 1) delta bias h out f. entailer!. }
  Intros out. forward.
  assert (Hfit: RefRt.encode_fits cps (Zlength oinit) = true)
    by (unfold RefRt.encode_fits; rewrite H9; apply Z.leb_le; lia).
  Exists (bufv out (Zlength oinit) oinit). rewrite Hfit.
  unfold RefRt.encode_out, RefRt.encode_len. rewrite H9. replace (Zlength out <=? Zlength oinit) with true by lia.
  entailer!.
  - apply bufv_len; auto.
  - unfold bufv. auto.
Qed.
