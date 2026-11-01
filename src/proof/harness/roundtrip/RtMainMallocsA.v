(* Helper lemmas for MainMallocs.v (the piece stmt_mallocs of the main of harness/x_roundtrip.c): the encoding inside
   lab, what malloc(elen) returned, the model facts of the decoder call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Local Open Scope logic.

(* The rest of lab around the encoding at lab + 4. *)
Definition lab_rest (m L: Z) (plab: val) : mpred :=
  !! field_compatible (tarray tuchar (16 * m + 6)) [] plab &&
  (data_at Ews (tarray tuchar 4) (Zrepeat Vundef 4) plab *
   data_at Ews (tarray tuchar (16 * m + 2 - L)) (Zrepeat Vundef (16 * m + 2 - L)) (offset_val (4 + L) plab)).

Lemma lab_split (m: Z) (e: list Z) (plab: val):
  0 <= Zlength e <= 16 * m + 1 ->
  data_at Ews (tarray tuchar (16 * m + 6)) (lab_after_encode m e) plab
  |-- arr0 Ews tuchar (Zlength e) (vb e) (offset_val 4 plab) * lab_rest m (Zlength e) plab.
Proof.
  intros He. unfold lab_after_encode.
  assert (Hv: Zlength (vb e) = Zlength e) by (unfold vb; list_solve).
  assert_PROP (field_compatible (tarray tuchar (16 * m + 6)) [] plab) as FC by entailer!.
  rewrite (split3_data_at_Tarray_tuchar Ews (16 * m + 6) 4 (4 + Zlength e)) by (try lia; list_solve).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.mul_1_l, !Z.add_0_l.
  replace (sublist 0 4 _) with (Zrepeat Vundef 4) by list_solve.
  replace (sublist 4 (4 + Zlength e) _) with (vb e) by list_solve.
  replace (sublist (4 + Zlength e) (16 * m + 6) _) with (Zrepeat Vundef (16 * m + 2 - Zlength e)) by list_solve.
  replace (16 * m + 6 - (4 + Zlength e)) with (16 * m + 2 - Zlength e) by lia.
  replace (4 + Zlength e - 4) with (Zlength e) by lia.
  unfold arr0, lab_rest. destruct (Z.eq_dec (Zlength e) 0).
  - assert (e = []) by (apply Zlength_nil_inv; auto). subst e. rewrite Zlength_nil in *.
    sep_apply (data_at_zero_array_inv Ews tuchar (vb []) (offset_val 4 plab)); try reflexivity.
    entailer!.
  - entailer!.
Qed.

Lemma lab_join (m: Z) (e: list Z) (plab: val):
  0 <= Zlength e <= 16 * m + 1 ->
  arr0 Ews tuchar (Zlength e) (vb e) (offset_val 4 plab) * lab_rest m (Zlength e) plab
  |-- data_at Ews (tarray tuchar (16 * m + 6)) (lab_after_encode m e) plab.
Proof.
  intros He. unfold lab_after_encode, lab_rest.
  assert (Hv: Zlength (vb e) = Zlength e) by (unfold vb; list_solve).
  Intros. rename H into FC.
  rewrite (split3_data_at_Tarray_tuchar Ews (16 * m + 6) 4 (4 + Zlength e)) by (try lia; list_solve).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.mul_1_l, !Z.add_0_l.
  replace (sublist 0 4 _) with (Zrepeat Vundef 4) by list_solve.
  replace (sublist 4 (4 + Zlength e) _) with (vb e) by list_solve.
  replace (sublist (4 + Zlength e) (16 * m + 6) _) with (Zrepeat Vundef (16 * m + 2 - Zlength e)) by list_solve.
  replace (16 * m + 6 - (4 + Zlength e)) with (16 * m + 2 - Zlength e) by lia.
  replace (4 + Zlength e - 4) with (Zlength e) by lia.
  unfold arr0. destruct (Z.eq_dec (Zlength e) 0).
  - assert (e = []) by (apply Zlength_nil_inv; auto). subst e. rewrite Zlength_nil in *.
    rewrite (data_at_zero_array_eq Ews tuchar (vb []) (offset_val 4 plab)); [ | reflexivity | auto with field_compatible | reflexivity ].
    entailer!.
  - entailer!.
Qed.

(* What malloc(n) returned, past the NULL test: an array of n octets (none when n = 0). *)
Lemma malloc_arr0_tuchar (n: Z) (p: val):
  0 <= n -> (p <> nullval \/ n = 0) ->
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  |-- arr0 Ews tuchar n (Zrepeat Vundef n) p * TT.
Proof.
  intros Hn Hp. unfold arr0. destruct (eq_dec p nullval).
  - destruct Hp as [Hp | ->]; [ contradiction | ]. rewrite if_true by auto. entailer!.
  - destruct (Z.eq_dec n 0); [ entailer! | ]. unfold data_at_, field_at_. entailer!.
Qed.

(* The octets of the encoding. *)
Lemma enc_bytes_ok (cps e: list Z):
  encode_chars_stmt -> Forall (fun c => 0 <= c <= 1114111) cps -> encode cps = Some e -> bytes_ok e.
Proof.
  intros EC Hc He. unfold bytes_ok.
  assert (Hc': Forall (fun c => 0 <= c <= Int.max_unsigned) cps).
  { eapply Forall_impl; [ | exact Hc ]. intros c Hc1. simpl in Hc1. rep_lia. }
  pose proof (EC cps e Hc' He) as Hf.
  rewrite Forall_forall in *. intros c Hin. specialize (Hf c Hin).
  destruct Hf as [-> | [ ? | [ ? | [? Hin'] ] ] ]; try rep_lia.
  specialize (Hc c Hin'). simpl in Hc. rep_lia.
Qed.

(* The decoder's result on the encoding, with exactly m = |cps| slots. *)
Lemma enc_decode_result (cps e: list Z) (init: list val):
  decode_encode_stmt -> Zlength cps <= 512 -> Forall (fun c => 0 <= c <= 1114111) cps -> encode cps = Some e ->
  Zlength e <= 16 * Zlength cps + 1 -> Zlength init = Zlength cps ->
  OpensslPunycode.proof.punycode.PunySpec.decode_result e (Zlength cps) init = (1, vb cps, Zlength cps).
Proof.
  intros DE Hm Hc He Hl Hi. unfold OpensslPunycode.proof.punycode.PunySpec.decode_result.
  rewrite (proj2 (Z.leb_gt _ _)) by rep_lia.
  rewrite (DE cps e (Zlength cps)) by (unfold label_cap; lia || auto).
  rewrite sublist_nil_gen by lia. rewrite app_nil_r. reflexivity.
Qed.

(* The value of (n != 0) for a size_t n. *)
Lemma cmpu_ne0 (n: Z): 0 <= n <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cne (Int64.repr n) (Int64.repr 0)) = Vint (Int.repr (if n =? 0 then 0 else 1)).
Proof.
  intros Hn. unfold Int64.cmpu. destruct (Z.eqb_spec n 0).
  - subst. reflexivity.
  - rewrite Int64.eq_false; [ reflexivity | intro E; apply repr_inj_unsigned64 in E; rep_lia ].
Qed.

(* What malloc returned, kept opaque to the automation during the NULL tests. *)
Definition mblock (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p.

Lemma mblock_tc (t: type) (p: val) (P: mpred):
  0 <= sizeof t -> mblock t p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof. intros. apply malloc_tc_test; auto. Qed.

(* (p == NULL && n != 0) as an integer. *)
Definition nz (p: val) (n: Z) : Z := if eq_dec p nullval then (if n =? 0 then 0 else 1) else 0.
Arguments nz : simpl never.

Lemma nz_null (n: Z): 0 <= n <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cne (Int64.repr n) (Int64.repr 0)) = Vint (Int.repr (nz nullval n)).
Proof. intros. unfold nz. rewrite if_true by auto. apply cmpu_ne0; auto. Qed.

Lemma nz_nonnull (p: val) (n: Z): p <> nullval -> nz p n = 0.
Proof. intros. unfold nz. rewrite if_false by auto. reflexivity. Qed.

Lemma nz_01 (p: val) (n: Z): nz p n = 0 \/ nz p n = 1.
Proof. unfold nz. destruct (eq_dec p nullval); [ destruct (n =? 0) | ]; auto. Qed.

Lemma nz_0 (p: val) (n: Z): nz p n = 0 -> p <> nullval \/ n = 0.
Proof.
  unfold nz. destruct (eq_dec p nullval); [ | auto ]. destruct (Z.eqb_spec n 0); [ auto | discriminate ].
Qed.
