(* pr_encode: the main loop (one round per code point >= 128) and the end (olen, return 1). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.proof.harness.EncRound.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Local Open Scope logic.

Definition stmt_main := (Ssequence
                  (Swhile
                    (Ebinop Olt (Etempvar _h tulong) (Etempvar _m tulong)
                      tint)
                    stmt_round)
                  (Ssequence
                    (Sassign (Ederef (Etempvar _olen (tptr tulong)) tulong)
                      (Etempvar _out tulong))
                    (Sreturn (Some (Econst_int (Int.repr 1) tint))))).

Lemma enc_main: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl,
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  0 <= Zlength (filter (fun c => c <? 128) cps) -> Zlength (filter (fun c => c <? 128) cps) <= Zlength cps -> Zlength (filter (fun c => c <? 128) cps) <= ocap ->
  Zlength (if 0 <? Zlength (filter (fun c => c <? 128) cps) then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps) <= ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _out (Vlong (Int64.repr (Zlength (if 0 <? Zlength (filter (fun c => c <? 128) cps) then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps))));
      temp _h (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) cps)))); temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) cps))));
      temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv (if 0 <? Zlength (filter (fun c => c <? 128) cps) then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps) ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_main (enc_post shc pc cps sho po ocap oinit shl pl).
Proof.
  intros. rename H into SH, H0 into SH0, H1 into SH1, H2 into H, H3 into H0, H4 into H1, H5 into H2,
    H6 into HB0, H7 into HB1, H8 into H3, H9 into H4.
  unfold stmt_main, enc_post. abbreviate_semax.
forward_while (enc_inv shc pc cps sho po ocap oinit shl pl (Zlength (filter (fun c => c <? 128) cps))).
{ unfold enc_inv.
  Exists 128 0 72 (Zlength (filter (fun c => c <? 128) cps))
    (if 0 <? Zlength (filter (fun c => c <? 128) cps) then filter (fun c => c <? 128) cps ++ [45]
     else filter (fun c => c <? 128) cps) (S (length cps)).
  entailer!. rewrite Nat2Z.inj_succ, <- Zlength_correct. lia. }
{ entailer!. }
{ pose proof (cnt_lt_le n cps). fix_cmp. try (unfold MORE_COMMANDS, abbreviate).
  eapply semax_post; [ | | | | apply (enc_round shc pc cps sho po ocap oinit shl pl
    (Zlength (filter (fun c => c <? 128) cps)) n delta bias h out f); auto; lia].
  2: apply brk_enc. 2: apply cont_enc.
  2: (intros; apply ENTAIL_refl).
  unfold POSTCONDITION, abbreviate. rewrite RA_normal_oP, RA_normal_loop1.
  unfold enc_inv. Intros n' d' b' h' o' f'. Exists (n', d', b', h', o', f'). entailer!; apply derives_refl. }
pose proof (cnt_lt_le n cps). fix_cmp.
destruct f as [|f]; [simpl in H6; lia|].
rewrite enc_rounds_done in H5 by lia.
subst ocap.
assert (Hfit: encode_fits cps (Zlength oinit) = true) by (unfold encode_fits; rewrite H5; apply Z.leb_le; lia).
forward. forward.
Exists (bufv out (Zlength oinit) oinit). rewrite Hfit.
unfold encode_out, encode_len. rewrite H5. replace (Zlength out <=? Zlength oinit) with true by lia.
entailer!.
- apply bufv_len; auto.
- unfold bufv. auto.
Qed.
