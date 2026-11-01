(* Plain-Coq lemmas about the decoder of the model (Model.decode) used by the body of ossl_punycode_decode. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.

Lemma last_delim_from_app: forall l1 l2 j acc,
  last_delim_from (l1 ++ l2) j acc = last_delim_from l2 (j + Zlength l1) (last_delim_from l1 j acc).
Proof.
  induction l1; intros; simpl.
  - rewrite Zlength_nil. f_equal; lia.
  - rewrite IHl1, Zlength_cons. f_equal; lia.
Qed.

Lemma last_delim_snoc: forall l j, 0 <= j < Zlength l ->
  last_delim (sublist 0 (j + 1) l) = if Znth j l =? 45 then j else last_delim (sublist 0 j l).
Proof.
  intros. unfold last_delim.
  rewrite (sublist_split 0 j (j + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite last_delim_from_app. simpl. rewrite Zlength_sublist by lia.
  replace (0 + (j - 0)) with j by lia. reflexivity.
Qed.

Lemma last_delim_from_range: forall l j acc, 0 <= acc -> 0 <= j -> (acc = 0 \/ acc < j) ->
  0 <= last_delim_from l j acc /\ (last_delim_from l j acc = 0 \/ last_delim_from l j acc < j + Zlength l).
Proof.
  induction l; intros; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons. destruct (IHl (j + 1) (if a =? 45 then j else acc)); [destruct (a =? 45); lia | lia
      | destruct (a =? 45); lia | ]. lia.
Qed.

Lemma last_delim_range: forall l, 0 <= last_delim l /\ (last_delim l = 0 \/ last_delim l < Zlength l).
Proof. intros. unfold last_delim. pose proof (last_delim_from_range l 0 0). lia. Qed.

Lemma last_delim_char: forall l, 0 < last_delim l -> Znth (last_delim l) l = 45.
Proof.
  intros l. unfold last_delim.
  assert (forall l j acc, 0 <= j -> 0 <= acc < j -> 0 < last_delim_from l j acc ->
    (last_delim_from l j acc = acc) \/ (j <= last_delim_from l j acc /\
      Znth (last_delim_from l j acc - j) l = 45)).
  { induction l0; intros; simpl in *. lia.
    destruct (a =? 45) eqn:E.
    - destruct (IHl0 (j + 1) j) as [-> | [? ?]]; try lia.
      + right. replace (j - j) with 0 by lia. rewrite Znth_0_cons. lia.
      + right. split. lia. rewrite Znth_pos_cons by lia. replace (_ - j - 1) with (last_delim_from l0 (j + 1) j - (j + 1)) by lia. auto.
    - destruct (IHl0 (j + 1) acc) as [-> | [? ?]]; try lia. auto.
      right. split. lia. rewrite Znth_pos_cons by lia. replace (_ - j - 1) with (last_delim_from l0 (j + 1) acc - (j + 1)) by lia. auto. }
  intros. destruct l as [|a l]. simpl in H0. lia.
  simpl in *. replace (if a =? 45 then 0 else 0) with 0 in * by (destruct (a =? 45); auto).
  destruct (H l 1 0) as [? | [? ?]]; try lia.
  rewrite Znth_pos_cons by lia. auto.
Qed.

Lemma basic_prefix_all: forall l, Forall (fun c => c < 128) l -> basic_prefix l = l.
Proof.
  induction l; intros; simpl; auto. inv H. destruct (a <? 128) eqn:E; [ | apply Z.ltb_ge in E; lia].
  f_equal. auto.
Qed.

Lemma basic_prefix_stop: forall l j, 0 <= j < Zlength l -> Forall (fun c => c < 128) (sublist 0 j l) ->
  128 <= Znth j l -> basic_prefix l = sublist 0 j l.
Proof.
  induction l; intros. rewrite Zlength_nil in H. lia.
  rewrite Zlength_cons in H. simpl.
  destruct (Z.eq_dec j 0).
  - subst. rewrite Znth_0_cons in H1. destruct (a <? 128) eqn:E; [apply Z.ltb_lt in E; lia | ].
    rewrite sublist_nil. auto.
  - rewrite sublist_0_cons in H0 |- * by lia. inv H0.
    destruct (a <? 128) eqn:E; [ | apply Z.ltb_ge in E; lia]. f_equal.
    apply IHl; auto. lia. rewrite Znth_pos_cons in H1 by lia. auto.
Qed.

Lemma adapt_loop_bound: forall f d k, 0 <= d -> 0 <= k ->
  0 <= adapt_loop f d k <= k + 36 * Z.of_nat f + 35.
Proof.
  assert (D: forall d, 0 <= d -> 0 <= 36 * d / (d + 38) <= 35).
  { intros. split. apply Z.div_pos; lia. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
  induction f; intros; cbn [adapt_loop].
  - specialize (D d H). lia.
  - destruct (455 <? d).
    + specialize (IHf (d / 35) (k + 36)). rewrite Nat2Z.inj_succ.
      assert (0 <= d / 35) by (apply Z.div_pos; lia). lia.
    + specialize (D d H). lia.
Qed.

Lemma adapt_bound: forall d np ft, 0 <= d -> 1 <= np -> 0 <= adapt d np ft <= 2340.
Proof.
  intros. unfold adapt.
  assert (0 <= (if ft then d / 700 else d / 2)) by (destruct ft; apply Z.div_pos; lia).
  set (d1 := if ft then d / 700 else d / 2) in *.
  assert (0 <= d1 / np) by (apply Z.div_pos; lia).
  pose proof (adapt_loop_bound 64 (d1 + d1 / np) 0). simpl Z.of_nat in H3. lia.
Qed.

Lemma div_test: forall x d w, 0 <= x -> 0 < w -> (x / w < d <-> x < d * w).
Proof.
  intros. split; intros.
  - pose proof (Z.mul_div_le x w H0). pose proof (Z.mod_pos_bound x w H0).
    rewrite (Z.div_mod x w) at 1 by lia. nia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma digit_value_range: forall c, 0 <= digit_value c <= 36.
Proof.
  intros. unfold digit_value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:?E end;
  rewrite ?andb_true_iff, ?Z.leb_le in *; lia.
Qed.

Lemma decode_result_eq: forall inp cap init ok out,
  Zlength inp < Int.max_unsigned -> decode inp cap = (ok, out) ->
  decode_result inp cap init =
    (if ok then 1 else 0, vb out ++ sublist (Zlength out) cap init, if ok then Zlength out else cap).
Proof.
  intros. unfold decode_result. destruct (Int.max_unsigned <=? Zlength inp) eqn:E.
  apply Z.leb_le in E. lia. rewrite H0. auto.
Qed.

(* The decoder after the basic code points. *)
Lemma decode_fail_cap: forall inp cap, cap < last_delim inp -> decode inp cap = (false, []).
Proof. intros. unfold decode. cbv zeta. rewrite (proj2 (Z.ltb_lt _ _) H). auto. Qed.

Lemma decode_fail_basic: forall inp cap j, last_delim inp <= cap -> 0 <= j < last_delim inp ->
  Forall (fun c => c < 128) (sublist 0 j inp) -> 128 <= Znth j inp ->
  decode inp cap = (false, sublist 0 j inp).
Proof.
  intros. pose proof (last_delim_range inp). pose proof (Zlength_nonneg inp).
  unfold decode. cbv zeta. rewrite (proj2 (Z.ltb_ge cap (last_delim inp))) by lia.
  rewrite (basic_prefix_stop _ j); rewrite ?Zlength_sublist by lia; try lia.
  - rewrite sublist_sublist00 by lia. rewrite Zlength_sublist by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. auto.
  - rewrite sublist_sublist00 by lia. auto.
  - rewrite Znth_sublist by lia. rewrite Z.add_0_r. auto.
Qed.

Lemma decode_basic: forall inp cap, last_delim inp <= cap ->
  Forall (fun c => c < 128) (sublist 0 (last_delim inp) inp) ->
  decode inp cap = steps inp (length inp) cap (if last_delim inp =? 0 then 0 else last_delim inp + 1) 128 0 72
    (sublist 0 (last_delim inp) inp).
Proof.
  intros. pose proof (last_delim_range inp). pose proof (Zlength_nonneg inp).
  unfold decode. cbv zeta. rewrite (proj2 (Z.ltb_ge cap (last_delim inp))) by lia.
  rewrite basic_prefix_all by auto. rewrite Zlength_sublist by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. auto.
Qed.

(* The insertion loop of I2: the array shifted from position j on. *)
Lemma shift_step: forall (A: list val) c j, 0 < j <= c -> c < Zlength A ->
  upd_Znth j (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) (Zlength A) A) (Znth (j - 1) A) =
  sublist 0 (j - 1 + 1) A ++ sublist (j - 1) c A ++ sublist (c + 1) (Zlength A) A.
Proof. intros. list_solve. Qed.

Lemma shift_read: forall (A: list val) c j, 0 < j <= c -> c < Zlength A ->
  Znth (j - 1) (sublist 0 (j + 1) A ++ sublist j c A ++ sublist (c + 1) (Zlength A) A) = Znth (j - 1) A.
Proof. intros. list_solve. Qed.

Lemma shift_insert: forall (out: list Z) (init: list val) cap i x, 0 <= i <= Zlength out -> Zlength out < cap ->
  Zlength init = cap ->
  let A := vb out ++ sublist (Zlength out) cap init in
  upd_Znth i (sublist 0 (i + 1) A ++ sublist i (Zlength out) A ++ sublist (Zlength out + 1) (Zlength A) A)
    (Vint (Int.repr x)) =
  vb (insert_at i x out) ++ sublist (Zlength (insert_at i x out)) cap init.
Proof.
  intros. subst A. unfold insert_at, vb in *. list_solve.
Qed.

Lemma shift_init: forall (A: list val) c, 0 <= c < Zlength A ->
  A = sublist 0 (c + 1) A ++ sublist c c A ++ sublist (c + 1) (Zlength A) A.
Proof. intros. list_solve. Qed.

Lemma basic_store: forall (inp: list Z) (init: list val) cap j, 0 <= j < cap -> j < Zlength inp ->
  Zlength init = cap ->
  upd_Znth j (vb (sublist 0 j inp) ++ sublist j cap init) (Vint (Int.repr (Znth j inp))) =
  vb (sublist 0 (j + 1) inp) ++ sublist (j + 1) cap init.
Proof. intros. unfold vb. list_solve. Qed.

Lemma Forall_sublist_snoc: forall (P: Z -> Prop) l j, 0 <= j < Zlength l -> Forall P (sublist 0 j l) ->
  P (Znth j l) -> Forall P (sublist 0 (j + 1) l).
Proof.
  intros. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite sublist_len_1 by lia.
  apply Forall_app. split; auto.
Qed.

(* One step of the digit loop, with the exact fuel. *)
Lemma digits_step: forall inp pos i w k bias, 0 <= pos < Zlength inp ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i w k bias =
  (let d := digit_value (Znth pos inp) in
   if 36 <=? d then None else
   let i1 := i + d * w in
   if maxint <? i1 then None else
   let t := threshold k bias in
   if d <? t then Some (i1, pos + 1) else
   let w1 := w * (36 - t) in
   if maxint <? w1 then None else
   digits inp (Z.to_nat (Zlength inp - (pos + 1))) (pos + 1) i1 w1 (k + 36) bias).
Proof.
  intros. replace (Z.to_nat (Zlength inp - pos)) with (S (Z.to_nat (Zlength inp - (pos + 1)))) by lia.
  cbn [digits]. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

Lemma digits_end: forall inp pos i w k bias, Zlength inp <= pos ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i w k bias = None.
Proof. intros. replace (Z.to_nat (Zlength inp - pos)) with O by lia. reflexivity. Qed.

Lemma steps_none: forall inp f cap pos n i bias out, pos < Zlength inp -> Zlength inp - pos <= Z.of_nat f ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = None ->
  steps inp f cap pos n i bias out = (false, out).
Proof.
  intros. destruct f as [|f]. simpl in H0. lia.
  cbn [steps]. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite H1. reflexivity.
Qed.

Lemma steps_some: forall inp f cap pos n i bias out i1 pos1, pos < Zlength inp -> Zlength inp - pos <= Z.of_nat f ->
  digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1) ->
  exists f', Zlength inp - pos - 1 <= Z.of_nat f' /\
  steps inp f cap pos n i bias out =
    (let c := Zlength out in
     let bias1 := adapt (i1 - i) (c + 1) (i =? 0) in
     let n1 := n + i1 / (c + 1) in
     if maxint <? n1 then (false, out) else
     let i2 := i1 mod (c + 1) in
     if cap <=? c then (false, out) else
     steps inp f' cap pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out)).
Proof.
  intros. destruct f as [|f]. simpl in H0. lia.
  exists f. split. lia.
  cbn [steps]. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite H1. reflexivity.
Qed.

Lemma steps_done: forall inp f cap pos n i bias out, Zlength inp <= pos ->
  steps inp f cap pos n i bias out = (true, out).
Proof.
  intros. destruct f as [|f]; cbn [steps]; auto. rewrite (proj2 (Z.leb_le _ _)) by lia. auto.
Qed.

Lemma threshold_range: forall k bias, 1 <= threshold k bias <= 26.
Proof.
  intros. unfold threshold.
  destruct (k <=? bias) eqn:E1; [lia|]. destruct (bias + 26 <=? k) eqn:E2; [lia|].
  apply Z.leb_gt in E1. apply Z.leb_gt in E2. lia.
Qed.
