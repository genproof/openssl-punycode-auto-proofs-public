(* Lemmas for the main of harness/rfc_samples.c: taking the literal of one sample out of all of them, its octets as
   the unsigned array ossl_punycode_decode reads, the code points of one sample in decoded[], what
   ossl_punycode_decode gives on a sample, and the blocks of any_uints. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Local Open Scope logic.

Lemma Znth_idx19 s : 0 <= s < 19 -> Znth s idx19 = s.
Proof.
  intros Hs. replace s with (Z.of_nat (Z.to_nat s)) by lia.
  assert (Z.to_nat s < 19)%nat as Hn by lia. revert Hn. generalize (Z.to_nat s) as n. intros n Hn.
  do 19 (destruct n as [ | n]; [ reflexivity | ]). lia.
Qed.

Lemma sep_list_app f l1 l2 : sep_list f (l1 ++ l2) = sep_list f l1 * sep_list f l2.
Proof.
  induction l1 as [ | a l1 IH]; simpl; [ rewrite emp_sepcon; auto | rewrite IH, sepcon_assoc; auto ].
Qed.

(* The literal of sample s, out of all of them. *)
Lemma lits_split gv s : 0 <= s < 19 -> lits gv = lit gv s * lits_but gv s.
Proof.
  intros Hs. unfold lits, lits_but.
  assert (Hl: Zlength idx19 = 19) by reflexivity.
  transitivity (sep_list (lit gv) (sublist 0 s idx19 ++ sublist s (s + 1) idx19 ++ sublist (s + 1) 19 idx19)).
  { f_equal. rewrite <- !sublist_split by lia. rewrite sublist_same by lia. reflexivity. }
  rewrite !sep_list_app. rewrite sublist_len_1 by lia. rewrite Znth_idx19 by lia. simpl.
  rewrite sepcon_emp. apply pred_ext; cancel.
Qed.

(* The NUL that ends the literal of sample s, at p. *)
Definition lit_nul (s: Z) (p: val) : mpred :=
  data_at Ers (Tarray tschar 1 noattr) [Vint (Int.repr 0)]
    (field_address0 (Tarray tschar (Zlength (enc s) + 1) noattr) [ArraySubsc (Zlength (enc s))] p).

Lemma sbyte_basic (l: list Z) : Forall (fun b => 0 < b < 128) l ->
  map (fun b => Vint (Int.repr (sbyte b))) l = vb l.
Proof.
  induction 1 as [ | b l Hb _ IH]; [ reflexivity | ]. simpl. rewrite IH. unfold sbyte.
  destruct (b <? 128) eqn:E; [ reflexivity | apply Z.ltb_ge in E; lia ].
Qed.

(* The literal of sample s at p: its octets as the unsigned array ossl_punycode_decode reads, and its NUL. *)
Lemma lit_arr s p : 0 <= s < 19 ->
  data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) p =
  arr0 Ers tuchar (Zlength (enc s)) (vb (enc s)) p * lit_nul s p.
Proof.
  intros Hs. destruct (sample_facts s Hs) as (_ & Hb & Hl & _).
  unfold lit_nul, arr0. rewrite if_false by lia.
  rewrite (split2_data_at_Tarray_tschar Ers (Zlength (enc s) + 1) (Zlength (enc s)))
    by (rewrite ?Zlength_vb, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
  rewrite vb_app. rewrite sublist_app1 by (rewrite ?Zlength_vb; lia).
  rewrite sublist_same by (rewrite ?Zlength_vb; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_vb; lia). rewrite Zlength_vb.
  replace (Zlength (enc s) + 1 - Zlength (enc s)) with 1 by lia.
  rewrite Z.sub_diag. rewrite sublist_same by reflexivity.
  f_equal.
  rewrite data_at_tuchar_tschar.
  - rewrite sbyte_basic by exact Hb. reflexivity.
  - eapply Forall_impl; [ | exact Hb ]. simpl. intros; rep_lia.
Qed.

(* decoded[] around the code points of sample s. *)
Definition dec_rest (gv: globals) (s: Z) : mpred :=
  data_at Ers (Tarray tuint (start s) noattr) (vb (sublist 0 (start s) dec)) (gv _decoded) *
  data_at Ers (Tarray tuint (355 - (start s + Znth s pts)) noattr) (vb (sublist (start s + Znth s pts) 355 dec))
    (field_address0 (Tarray tuint 355 noattr) [ArraySubsc (start s + Znth s pts)] (gv _decoded)).

Lemma decoded_split gv s : 0 <= s < 19 ->
  decoded_at gv =
  arr0 Ers tuint (Znth s pts) (vb (expected s))
    (field_address0 (Tarray tuint 355 noattr) [ArraySubsc (start s)] (gv _decoded)) * dec_rest gv s.
Proof.
  intros Hs. pose proof (start_bound s Hs). pose proof (Znth_pts_range s Hs). pose proof Zlength_dec.
  unfold decoded_at, dec_rest, arr0, expected. rewrite if_false by lia.
  assert (Hv: Zlength (vb dec) = 355) by (rewrite Zlength_vb; lia).
  rewrite (split3_data_at_Tarray Ers tuint 355 (start s) (start s + Znth s pts) (vb dec) (vb dec)
    (vb (sublist 0 (start s) dec)) (vb (sublist (start s) (start s + Znth s pts) dec))
    (vb (sublist (start s + Znth s pts) 355 dec)));
    change (@reptype CS tuint) with val in *.
  - replace (start s + Znth s pts - start s) with (Znth s pts) by lia.
    apply pred_ext; cancel.
  - hnf; auto.
  - lia.
  - lia.
  - rewrite sublist_same by lia. reflexivity.
  - unfold vb. rewrite sublist_map. reflexivity.
  - unfold vb. rewrite sublist_map. reflexivity.
  - unfold vb. rewrite sublist_map. reflexivity.
Qed.

(* The address decoded + a. *)
Lemma decoded_address (q: val) a : field_compatible (tarray tuint 355) [] q -> 0 <= a <= 355 ->
  field_address0 (Tarray tuint 355 noattr) [ArraySubsc a] q = offset_val (4 * a) q.
Proof.
  intros Hf Ha. rewrite field_address0_offset.
  - simpl. f_equal.
  - apply arr_field_compatible0; [ exact Hf | lia ].
Qed.

(* What ossl_punycode_decode gives on sample s into exactly points[s] code points. *)
Lemma decode_result_sample s (init: list val) : 0 <= s < 19 -> Zlength init = Znth s pts ->
  OpensslPunycode.proof.punycode.PunySpec.decode_result (enc s) (Znth s pts) init =
  (1, vb (expected s), Znth s pts).
Proof.
  intros Hs Hi. destruct (sample_facts s Hs) as (_ & _ & Hl & Hd).
  unfold OpensslPunycode.proof.punycode.PunySpec.decode_result.
  destruct (Int.max_unsigned <=? Zlength (enc s)) eqn:E; [ apply Z.leb_le in E; rep_lia | ].
  rewrite Hd. rewrite Zlength_expected by exact Hs. rewrite <- Hi, sublist_nil, app_nil_r. reflexivity.
Qed.

Lemma expected_range s : Forall (fun x => 0 <= x <= Int.max_unsigned) (expected s).
Proof. unfold expected. apply Forall_sublist. exact dec_range. Qed.

(* What free(out) wants, from the block of any_uints (whose specification is stated under the helpers'
   compspecs). *)
Lemma free_pre (p: val) n v : p <> nullval -> 0 < n ->
  @malloc_token OpensslPunycode.proof.laws.common.HelperSpec.CS Ews (tarray tuint n) p *
  @arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuint n v p |--
  if eq_dec p nullval then emp else @malloc_token CS Ews (tarray tuint n) p * @data_at_ CS Ews (tarray tuint n) p.
Proof.
  intros Hp Hn. rewrite if_false by auto. unfold arr0. rewrite if_false by lia.
  rewrite (@malloc_token_change_composite OpensslPunycode.proof.laws.common.HelperSpec.CS CS (CCE_any _ _)
    Ews (tarray tuint n) eq_refl).
  sep_apply (@data_at_data_at_ OpensslPunycode.proof.laws.common.HelperSpec.CS Ews (tarray tuint n) v p).
  rewrite (@data_at__change_composite OpensslPunycode.proof.laws.common.HelperSpec.CS CS (CCE_any _ _)
    Ews (tarray tuint n) eq_refl).
  cancel.
Qed.

(* A block from malloc that may be NULL: its token and its contents (as arr0), each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition mtok {cs: compspecs} (t: type) (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p.
Definition marr {cs: compspecs} (t: type) (n: Z) (v: list (reptype t)) (p: val) : mpred :=
  if eq_dec p nullval then emp else arr0 Ews t n v p.

Lemma split_block {cs: compspecs} t n v p:
  complete_legal_cosu_type t = true ->
  (if eq_dec p nullval then emp else malloc_token Ews (tarray t n) p * data_at Ews (tarray t n) v p)
  |-- mtok t n p * marr t n v p.
Proof.
  intros Ht. unfold mtok, marr. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  unfold arr0. destruct (Z.eq_dec n 0); [ subst; entailer! | cancel ].
  apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_inv; auto.
Qed.

(* The test p == NULL of such a block is defined. *)
Lemma block_tc_test {cs: compspecs} t n v p P:
  (0 < n -> sizeof (tarray t n) > 0) -> sizeof (tarray t 0) <= 0 -> 0 <= n ->
  mtok t n p * marr t n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht H0 Hn. unfold mtok, marr. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - unfold arr0. destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray t 0) p). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray t n) v p); [ apply readable_nonidentity; auto | apply Ht; lia | ].
      entailer!.
Qed.
