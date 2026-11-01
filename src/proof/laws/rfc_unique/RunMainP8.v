(* Piece 8 of the main of harness/rfc_unique.c: count1 = count2 = cap, the two calls of ossl_punycode_decode and the
   test `r1 != 1 || r2 != 1 || count1 != count2 || !uints_eq(out1, out2, count1)` (RunMainDefs).  Past the test
   both inputs decode, with the same capacity, to the same code points, and the model fact gives pre13. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunMainDefs.
Require OpensslPunycode.proof.harness.ARDecRange.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification moves to the law's compspecs (its arrays are scalars). *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.

(* What ossl_punycode_decode leaves: 0, or 1 when Model.decode succeeds with out; then the array starts with out
   and the count is |out|. *)
Lemma dres_cases inp c init:
  bytes_ok inp -> 0 <= c ->
  fst (fst (PS.decode_result inp c init)) = 0 \/
  (fst (fst (PS.decode_result inp c init)) = 1 /\
   exists out, decode inp c = (true, out) /\ Zlength out <= c /\
     Forall (fun x => 0 <= x <= Int.max_unsigned) out /\
     snd (fst (PS.decode_result inp c init)) = vb out ++ sublist (Zlength out) c init /\
     snd (PS.decode_result inp c init) = Zlength out).
Proof.
  intros Hb Hc. unfold PS.decode_result.
  destruct (Int.max_unsigned <=? Zlength inp); [ left; reflexivity | ].
  pose proof (ARDecRange.decode_out_range inp c Hb Hc) as [Hr Hl].
  destruct (decode inp c) as [ok out] eqn:D. destruct ok; [ right | left; reflexivity ].
  simpl in Hr, Hl. split; [ reflexivity | ]. exists out. split; [ reflexivity | ]. split; [ exact Hl | ].
  split; [ | split; reflexivity ].
  eapply Forall_impl; [ | exact Hr ]. intros x Hx. unfold maxint in Hx. rep_lia.
Qed.

(* The first elements of an array of c unsigned ints are an array of their own. *)
Lemma arr0_prefix_ui {cs: compspecs} sh c (l1 l2: list val) q:
  Zlength l1 <= c -> Zlength l2 = c - Zlength l1 ->
  arr0 sh tuint c (l1 ++ l2) q |-- arr0 sh tuint (Zlength l1) l1 q * TT.
Proof.
  intros H1 H2. pose proof (Zlength_nonneg l1). unfold arr0.
  destruct (Z.eq_dec (Zlength l1) 0) as [E | E].
  - rewrite emp_sepcon. apply TT_right.
  - rewrite if_false by lia.
    rewrite (split2_data_at_Tarray_app (Zlength l1) c sh tuint l1 l2) by auto. cancel.
Qed.

Lemma piece8 : RunUniqStmt.unique_stmt -> piece13_stmt -> piece8_stmt.
Proof.
  intros Hu H13 Espec gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2. unfold pre8, T8, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward. forward.
  forward_call (gv, Ews, pi1, bs1, Ews, po1, c, vb vs1, Tsh, v1).
  { rewrite Zlength_vb; auto. }
  forward_call (gv, Ews, pi2, bs2, Ews, po2, c, vb vs2, Tsh, v2).
  { rewrite Zlength_vb; auto. }
  pose proof (dres_cases bs1 c (vb vs1) H ltac:(lia)) as C1.
  pose proof (dres_cases bs2 c (vb vs2) H0 ltac:(lia)) as C2.
  destruct (PS.decode_result bs1 c (vb vs1)) as [[r1 a1] n1].
  destruct (PS.decode_result bs2 c (vb vs2)) as [[r2 a2] n2].
  simpl fst in *; simpl snd in *.
  destruct C1 as [-> | [-> [out1 [D1 [Hl1 [Hr1 [-> ->]]]]]]].
  { (* the first decode fails *)
    forward_if (temp _t'13 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if (temp _t'14 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if (temp _t'15 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if; [ forward; Exists (Int.repr 0); entailer! | discriminate ]. }
  destruct C2 as [-> | [-> [out2 [D2 [Hl2 [Hr2 [-> ->]]]]]]].
  { (* the second decode fails *)
    forward_if (temp _t'13 (Vint Int.one)); [ discriminate | forward; entailer! | ].
    forward_if (temp _t'14 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if (temp _t'15 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if; [ forward; Exists (Int.repr 0); entailer! | discriminate ]. }
  forward_if (temp _t'13 (Vint Int.zero)); [ discriminate | forward; entailer! | ].
  pose proof (Zlength_nonneg out1). pose proof (Zlength_nonneg out2).
  destruct (Z.eq_dec (Zlength out1) (Zlength out2)) as [El | El].
  2: { (* different counts *)
    forward_if (temp _t'14 (Vint Int.one)); [ exfalso; lia | | ].
    { forward. forward. forward. entailer!. }
    forward_if (temp _t'15 (Vint Int.one)); [ forward; entailer! | discriminate | ].
    forward_if; [ forward; Exists (Int.repr 0); entailer! | discriminate ]. }
  forward_if (temp _t'14 (Vint Int.zero)); [ exfalso; lia | | ].
  { forward. forward. forward. entailer!. }
  forward_if (PROP () LOCAL (temp _t'15 (Vint (Int.repr (if list_eq_dec Z.eq_dec out1 out2 then 0 else 1)));
                             temp _input2 pi2; temp _len2 (Vlong (Int64.repr (Zlength bs2)));
                             temp _input1 pi1; temp _len1 (Vlong (Int64.repr (Zlength bs1)));
                             gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
              SEP (arr0 Ews tuchar (Zlength bs1) (vb bs1) pi1; arr0 Ews tuchar (Zlength bs2) (vb bs2) pi2;
                   data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; TT)).
  { exfalso; lia. }
  { forward.
    sep_apply (arr0_prefix_ui Ews c (vb out1) (sublist (Zlength out1) c (vb vs1)) po1).
    { rewrite Zlength_vb; lia. }
    { rewrite Zlength_sublist by (rewrite ?Zlength_vb; lia). rewrite !Zlength_vb; lia. }
    sep_apply (arr0_prefix_ui Ews c (vb out2) (sublist (Zlength out2) c (vb vs2)) po2).
    { rewrite Zlength_vb; lia. }
    { rewrite Zlength_sublist by (rewrite ?Zlength_vb; lia). rewrite !Zlength_vb; lia. }
    rewrite !Zlength_vb. Intros. rewrite <- El.
    rewrite (arr0_tuint_cs CS C.CS Ews (Zlength out1) _ po1).
    rewrite (arr0_tuint_cs CS C.CS Ews (Zlength out1) _ po2).
    forward_call (Ews, po1, out1, Ews, po2, out2).
    forward.
    entailer!.
    destruct (list_eq_dec Z.eq_dec out1 out2); reflexivity. }
  forward_if.
  { forward. Exists (Int.repr 0). entailer!. }
  destruct (list_eq_dec Z.eq_dec out1 out2) as [<- | NE]; [ | discriminate ].
  destruct (Hu bs1 bs2 c out1 H H0 D1 D2) as [Hlen Hj].
  eapply semax_pre; [ | apply (H13 Espec gv v1 v2 bs1 bs2 pi1 pi2) ].
  unfold pre13, same_up_to_case. entailer!.
Qed.
