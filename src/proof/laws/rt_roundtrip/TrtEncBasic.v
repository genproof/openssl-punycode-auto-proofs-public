(* encode: the copy of the basic code points (one iteration of the first loop: put cps[j] when it is < 128). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Local Open Scope logic.

(* The state of the copy loop before code point j (the temp j holds jv): the basic code points of cps[0..j). *)
Definition tbasic_st (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (j jv: Z) : environ -> mpred :=
  PROP (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) <= room)
  LOCAL (temp _j (Vlong (Int64.repr jv));
         temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar room (bufv (filter (fun c => c <? 128) (sublist 0 j cps)) room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps))))) pl).

Definition tstmt_basicbody := ltac:(let b := eval cbv delta [f_encode fn_body] beta iota in (fn_body f_encode) in
  match b with context [Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) ?x) (Sset _j _)] => exact x end).

Lemma tenc_basic_body: forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl (j: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> 4 * Zlength cps <= Int64.max_unsigned ->
  0 <= room <= Int64.max_unsigned -> Zlength oinit = room -> 0 <= j < Zlength cps ->
  semax TDelta (tbasic_st shc pc cps sho po room oinit shl pl j j) tstmt_basicbody
    (overridePost (tbasic_st shc pc cps sho po room oinit shl pl (j + 1) j)
      (tpost shc pc cps sho po room oinit shl pl)).
Proof.
  intros. unfold tbasic_st, tstmt_basicbody, tpost. abbreviate_semax. Intros.
  assert (Hc: 0 <= Znth j cps <= Int.max_unsigned) by (rewrite Forall_forall in H2; apply H2; apply Znth_In; lia).
  assert (Hv: @Znth val Vundef j (vb cps) = Vint (Int.repr (Znth j cps))) by (unfold vb; rewrite Znth_map by lia; auto).
  pose proof (filter_sublist_succ (fun c => c <? 128) cps j ltac:(lia)) as Hfs.
  cbv beta in Hfs.
  set (c := Znth j cps) in *.
  pose proof (Zlength_nonneg (filter (fun c => c <? 128) (sublist 0 j cps))) as Hbj.
  replace_SEP 0 (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc); [entailer!; apply arr0_data_at; lia |].
  forward. { entailer!. rewrite Hv. simpl. auto. }
  rewrite Hv.
  forward_if.
  - replace (c <? 128) with true in Hfs by lia.
    forward. { entailer!. rewrite Hv. simpl. auto. }
    rewrite Hv.
    replace_SEP 0 (arr0 shc tuint (Zlength cps) (vb cps) pc); [entailer!; apply data_at_arr0; lia |].
    set (bj := filter (fun c0 : Z => c0 <? 128) (sublist 0 j cps)) in *.
    forward_call (sho, po, room, bufv bj room oinit, shl, pl, Zlength bj, c).
    { apply bufv_len; lia. }
    destruct (Zlength bj <? room) eqn:Er; [apply Z.ltb_lt in Er | apply Z.ltb_ge in Er].
    { forward_if. { discriminate. } rewrite bufv_upd by lia.
      assert (E: Zlength bj + 1 = Zlength (bj ++ [c])) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      rewrite E, <- Hfs. forward. entailer!. rewrite Hfs, <- E. split; [lia | reflexivity]. }
    forward_if. 2: contradiction. forward.
    eapply derives_trans; [ | apply (tret0_entail cps _ oinit shc pc sho po shl pl (bufv bj (Zlength oinit) oinit)
      (Vlong (Int64.repr (Zlength bj)))) ]; [cancel | | apply bufv_len; lia].
    apply (encode_fits_basics cps _ (j + 1)); [lia |]. rewrite Hfs, Zlength_app, Zlength_cons, Zlength_nil. lia.
  - replace (c <? 128) with false in Hfs by lia. rewrite app_nil_r in Hfs.
    replace_SEP 0 (arr0 shc tuint (Zlength cps) (vb cps) pc); [entailer!; apply data_at_arr0; lia |].
    forward. rewrite Hfs. entailer!.
Qed.
