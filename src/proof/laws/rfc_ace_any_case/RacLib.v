(* Lemmas shared by the pieces of the main of harness/rfc_ace_any_case.c (RacMainDefs): the array of a string as the
   C string ossl_a2ulabel reads and the rest of the array; the outcomes of the two calls agree when the failure flags
   agree; the WPACKET record's zero-size token. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacModel.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacMainDefs.
Local Open Scope logic.

(* The position of the first NUL of t ++ [0] is within t ++ [0]. *)
Lemma rac_nul_lt t: 0 <= nul_len (t ++ [0]) <= Zlength t.
Proof.
  pose proof (nul_len_range (t ++ [0])) as R. rewrite Zlength_app, Zlength_cons, Zlength_nil in R.
  split; [ lia | ].
  destruct (zlt (Zlength t) (nul_len (t ++ [0]))) as [L | ]; [ exfalso | lia ].
  assert (E: nul_len (t ++ [0]) = Zlength t + 1) by lia.
  pose proof (nul_len_nonzero (t ++ [0])) as F. rewrite E in F.
  rewrite sublist_same in F by list_solve.
  apply Forall_app in F. destruct F as [_ F]. inv F. auto.
Qed.

(* The string of the array is a C string ossl_a2ulabel accepts (octets 1..255). *)
Lemma rstr_ok a b t: (a = 88 \/ a = 120) -> (b = 78 \/ b = 110) -> bytes_ok t -> ShimSpec.str_ok (rstr a b t).
Proof.
  intros Ha Hb Ht. unfold ShimSpec.str_ok, rstr. apply Forall_app. split.
  - destruct Ha, Hb; subst; repeat constructor; rep_lia.
  - pose proof (nul_len_nonzero (t ++ [0])) as F.
    assert (G: bytes_ok (t ++ [0])) by (apply Forall_app; split; [ auto | repeat constructor; rep_lia ]).
    apply (Forall_sublist _ 0 (nul_len (t ++ [0]))) in G.
    rewrite Forall_forall in *. intros x Hx. specialize (F x Hx). specialize (G x Hx). simpl in G. lia.
Qed.

(* The array of [a; b; '-'; '-'] ++ t ++ [0]: the C string rstr a b t, then the rest of the array. *)
Lemma rac_str_split sh a b t p:
  @data_at CS sh (tarray tuchar (Zlength t + 5)) (vb ([a; b; 45; 45] ++ t ++ [0])) p =
  (ShimSpec.cstr sh (rstr a b t) p *
   @data_at CS sh (tarray tuchar (Zlength t - nul_len (t ++ [0])))
     (vb (sublist (nul_len (t ++ [0]) + 1) (Zlength t + 1) (t ++ [0])))
     (@field_address0 CS (tarray tuchar (Zlength t + 5)) (SUB (nul_len (t ++ [0]) + 5)) p))%logic.
Proof.
  pose proof (rac_nul_lt t) as R. set (k := nul_len (t ++ [0])) in *.
  assert (Z0: Znth k (t ++ [0]) = 0) by (apply nul_len_at; fold k; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  unfold ShimSpec.cstr, rstr. fold k.
  rewrite (data_at_tuchar_cs ShimSpec.CS CS).
  assert (E: [a; b; 45; 45] ++ t ++ [0] =
             ([a; b; 45; 45] ++ sublist 0 k (t ++ [0]) ++ [0]) ++ sublist (k + 1) (Zlength t + 1) (t ++ [0])).
  { rewrite <- Z0. list_solve. }
  rewrite E at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (k + 5)).
  - replace (Zlength t + 5 - (k + 5)) with (Zlength t - k) by lia.
    replace (Zlength ([a; b; 45; 45] ++ sublist 0 k (t ++ [0])) + 1) with (k + 5) by list_solve.
    rewrite <- app_assoc. reflexivity.
  - list_solve.
  - list_solve.
Qed.

(* The failure flags of the two calls agree: then so do their results and buffers. *)
Lemma rac_outcome po1 po2 cap a b t ob mf1 mf2:
  po1 <> nullval -> po2 <> nullval -> (a = 88 \/ a = 120) -> (b = 78 \/ b = 110) ->
  snd (fst (outc po1 cap (rstr a b t) ob mf1)) = snd (fst (outc po2 cap (rstr 120 110 t) ob mf2)) ->
  fst (fst (fst (outc po1 cap (rstr a b t) ob mf1))) = fst (fst (fst (outc po2 cap (rstr 120 110 t) ob mf2))) /\
  snd (outc po1 cap (rstr a b t) ob mf1) = snd (outc po2 cap (rstr 120 110 t) ob mf2).
Proof.
  intros H1 H2 Ha Hb. unfold outc, PunySpec.a2u_outcome, rstr.
  rewrite (rac_a2ulabel a b _ cap Ha Hb).
  destruct (Val.eq po1 nullval); [ contradiction | ]. destruct (Val.eq po2 nullval); [ contradiction | ].
  destruct (cap =? 0); simpl; [ auto | ].
  match goal with |- context [a2ulabel ?s cap] => destruct (a2ulabel s cap) as [r w] end.
  destruct mf1, mf2; simpl; intros E; try discriminate; auto.
Qed.

(* The buffer after a call holds octet values. *)
Lemma rac_outcome_ints po cap s ob mf: Forall (fun v => exists i, v = Vint i) (snd (outc po cap s ob mf)).
Proof.
  assert (V: forall l, Forall (fun v => exists i, v = Vint i) (vb l)).
  { intros l. unfold vb. rewrite Forall_map. apply Forall_forall. intros. simpl. eauto. }
  unfold outc, PunySpec.a2u_outcome.
  destruct (Val.eq po nullval); [ apply V | ]. destruct (cap =? 0); [ apply V | ]. simpl.
  destruct mf; [ apply V | ]. destruct (a2ulabel s cap) as [r w]. simpl.
  apply Forall_app; split; [ apply V | apply Forall_sublist, V ].
Qed.

(* A buffer of octet values is the values of a list of octets. *)
Lemma rac_vb_fits sh n (vs: list val) p:
  Forall (fun v => exists i, v = Vint i) vs ->
  @data_at CS sh (tarray tuchar n) vs p |-- !! (exists L, bytes_ok L /\ vs = vb L).
Proof.
  intros HV. eapply derives_trans; [ apply data_at_local_facts | ]. apply prop_derives.
  intros [_ H0]. clear - HV H0.
  rewrite value_fits_eq in H0. simpl in H0. destruct H0 as [_ H0].
  exists (map (fun v => match v with Vint i => Int.unsigned i | _ => 0 end) vs).
  induction vs as [ | v vs IH]; [ split; [ constructor | reflexivity ] | ].
  inv HV. inv H0. destruct (IH H3 H5) as [IH1 IH2].
  destruct H2 as [i ->].
  rewrite value_fits_eq in H4. simpl in H4. unfold tc_val' in H4. simpl in H4.
  specialize (H4 ltac:(discriminate)).
  split.
  - constructor; auto. simpl. pose proof (Int.unsigned_range i). rep_lia.
  - simpl. rewrite <- IH2. f_equal. f_equal. rewrite Int.repr_unsigned. auto.
Qed.

(* The token of out1's block gives the zero-size token ossl_a2ulabel's buffer wants when outlen = 0, and stays
   whole otherwise. *)
Lemma rac_tok_split n p:
  @malloc_token HelperSpec.CS Ews (tarray tuchar n) p =
  (ShimSpec.zero_tok n (tarray tuchar 0) p *
   (if Z.eq_dec n 0 then emp else @malloc_token HelperSpec.CS Ews (tarray tuchar n) p))%logic.
Proof.
  unfold ShimSpec.zero_tok. destruct (Z.eq_dec n 0).
  - subst. rewrite sepcon_emp.
    rewrite (@malloc_token_change_composite HelperSpec.CS ShimSpec.CS (CCE_any _ _) Ews (tarray tuchar 0))
      by reflexivity. reflexivity.
  - rewrite emp_sepcon. reflexivity.
Qed.
