(* pr_encode: the copy of the basic code points (one iteration of the first loop). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.proof.harness.EncBasic2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_basic_body: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (j: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap -> 0 <= j < Zlength cps ->
  semax DeltaE (basic_st shc pc cps sho po ocap oinit shl pl j j) stmt_basicbody
    (overridePost (basic_st shc pc cps sho po ocap oinit shl pl (j + 1) j)
      (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros. rename H into SH, H0 into SH0, H1 into SH1, H2 into H, H3 into H0, H4 into H1, H5 into H2, H6 into H3.
  unfold basic_st, stmt_basicbody, enc_post. abbreviate_semax. Intros.
  assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H; apply H; apply Znth_In; lia).
  assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
  pose proof (filter_sublist_succ (fun c => c <? 128) cps j ltac:(lia)) as Hfs.
  cbv beta in Hfs.
  set (c := Znth j cps) in *.
  pose proof (Zlength_nonneg (filter (fun c => c <? 128) (sublist 0 j cps))) as Hbj.
  replace_SEP 0 (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc); [entailer!; apply arr0_data_at; lia |].
  forward. { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  replace_SEP 0 (arr0 shc tuint (Zlength cps) (vb cps) pc); [entailer!; apply data_at_arr0; lia |].
  forward_if.
  - replace (c <? 128) with true in Hfs by lia.
    unfold POSTCONDITION, abbreviate.
    eapply enc_basic_lt; eauto.
  - replace (c <? 128) with false in Hfs by lia. rewrite app_nil_r in Hfs.
    forward. rewrite Hfs. entailer!.
Qed.
