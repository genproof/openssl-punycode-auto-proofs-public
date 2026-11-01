(* Facts for the utf8 loop of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainP17): what the decoder leaves for the
   loop (Ru8MainDefs.dres), the length of the UTF-8 octets written so far, and the cut of want around the octets of
   one code point. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.punycode.A2uModel.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Local Open Scope Z_scope.

(* The UTF-8 octets of a code point are at most 4. *)
Lemma ru8p17_utf8_len: forall c, 0 <= Zlength (utf8 c) <= 4.
Proof.
  intros c. unfold utf8.
  destruct (c <? 128); [|destruct (c <? 2048); [|destruct (c <? 65536); [|destruct (c <=? 1114111)]]];
  simpl; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

(* The octets of l code points are at most 4 per code point. *)
Lemma ru8p17_concat_len: forall l, 0 <= Zlength (concat (map utf8 l)) <= 4 * Zlength l.
Proof.
  induction l as [|c l IH]; simpl.
  - rewrite Zlength_nil; lia.
  - rewrite Zlength_app, Zlength_cons. pose proof (ru8p17_utf8_len c). lia.
Qed.

(* One more code point: its octets after those of the earlier ones. *)
Lemma ru8p17_concat_step: forall (l: list Z) j, 0 <= j < Zlength l ->
  concat (map utf8 (sublist 0 (j + 1) l)) = concat (map utf8 (sublist 0 j l)) ++ utf8 (Znth j l).
Proof.
  intros l j Hj. rewrite (sublist_split 0 j (j + 1)) by lia.
  rewrite sublist_len_1 by lia. rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

(* Every code point at most 0x10FFFF, as ru8_want tests it. *)
Lemma ru8p17_forallb: forall l, Forall (fun c => c <= 1114111) l -> forallb (fun c => c <=? 1114111) l = true.
Proof.
  induction 1 as [|c l Hc _ IH]; simpl; auto.
  rewrite IH, andb_true_r. apply Z.leb_le; auto.
Qed.

(* A code point above 0x10FFFF: ru8_want's test fails. *)
Lemma ru8p17_forallb_false: forall l j, 0 <= j < Zlength l -> 1114111 < Znth j l ->
  forallb (fun c => c <=? 1114111) l = false.
Proof.
  intros l j Hj Hc. destruct (forallb (fun c => c <=? 1114111) l) eqn:E; auto.
  rewrite forallb_forall in E. specialize (E (Znth j l) ltac:(apply Znth_In; lia)).
  apply Z.leb_le in E. lia.
Qed.

(* What the decoder leaves for the loop: either valid = 0, count = 512, 512 values in cps and no decoding
   (ru8_want s = None), or valid = 1, the code points out (at most 512, each an unsigned int) at the start of cps,
   their number in count, and ru8_want is their UTF-8 form when every one is at most 0x10FFFF. *)
Lemma ru8p17_cases: forall s, bytes_ok s ->
  ((fst (fst (OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512))) =? 1) = false /\
   snd (OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512)) = 512 /\
   Zlength (snd (fst (OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512)))) = 512 /\
   ru8_want s = None) \/
  exists out,
    OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512) =
      (1, vb out ++ sublist (Zlength out) 512 (Zrepeat Vundef 512), Zlength out) /\
    Zlength out <= 512 /\ Forall (fun c => 0 <= c <= Int.max_unsigned) out /\
    ru8_want s = if forallb (fun c => c <=? 1114111) out then Some (concat (map utf8 out)) else None.
Proof.
  intros s OK. unfold OpensslPunycode.proof.punycode.PunySpec.decode_result, ru8_want.
  destruct (Int.max_unsigned <=? Zlength s) eqn:E. { left; simpl; repeat split; reflexivity. }
  pose proof (OpensslPunycode.proof.punycode.A2uModel.decode_out_range s 512 OK ltac:(lia)) as [F L].
  unfold label_cap. destruct (decode s 512) as [ok out]. simpl in F, L.
  destruct ok.
  2: { left; simpl; repeat split. unfold vb. rewrite Zlength_app, Zlength_map, Zlength_sublist; rewrite ?Zlength_Zrepeat; try lia.
       pose proof (Zlength_nonneg out). lia. }
  right. exists out. split; [reflexivity|]. split; [lia|]. split; [|reflexivity].
  eapply Forall_impl; [|exact F]. unfold maxint. simpl. rep_lia.
Qed.

(* want cut around the octets of one code point: [0, a), [a, a + b), the rest. *)
Lemma ru8p17_split3 {cs: compspecs}: forall sh n a b (l: list val) p,
  0 <= a -> 0 <= b -> a + b <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar a) (sublist 0 a l) p *
   data_at sh (tarray tuchar b) (sublist a (a + b) l) (offset_val a p) *
   data_at sh (tarray tuchar (n - (a + b))) (sublist (a + b) n l) (offset_val (a + b) p))%logic.
Proof.
  intros sh n a b l p Ha Hb Hn Hl Hfc.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a (a + b)) by lia.
  replace (a + b - a) with b by lia.
  rewrite !field_address0_offset.
  - simpl. replace (0 + 1 * a) with a by lia. replace (0 + 1 * (a + b)) with (a + b) by lia. reflexivity.
  - destruct Hfc as [? [? [? [? ?]]]]; repeat split; auto; simpl; lia.
  - destruct Hfc as [? [? [? [? ?]]]]; repeat split; auto; simpl; lia.
Qed.
