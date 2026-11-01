(* What the law rfc_basic_first checks of the decoder, as facts about Model.decode (plain Coq):
   - a literal octet (before the last '-') of 0x80 or more makes decode fail;
   - on success, the code points of the output below 0x80, in order, are the literal octets
     sublist 0 (last_delim inp) inp: the decoder starts from them and only inserts code points n >= 0x80
     (n starts at 128 and only grows). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.harness.ARDecRange.

Definition lt128 (x: Z) : bool := x <? 128.

(* The longest basic prefix stops at the first non-basic element. *)
Lemma rbf_basic_prefix_short: forall l i, 0 <= i < Zlength l -> 128 <= Znth i l ->
  Zlength (basic_prefix l) <= i.
Proof.
  induction l as [|a l IH]; intros i Hi Hn; [ rewrite Zlength_nil in Hi; lia | ].
  rewrite Zlength_cons in Hi. simpl.
  destruct (a <? 128) eqn:E.
  - destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth_0_cons in Hn. apply Z.ltb_lt in E. lia.
    + rewrite Znth_pos_cons in Hn by lia. rewrite Zlength_cons.
      specialize (IH (i - 1) ltac:(lia) Hn). lia.
  - rewrite Zlength_nil. lia.
Qed.

(* A basic prefix as long as the list is the list. *)
Lemma rbf_basic_prefix_full: forall l, Zlength l <= Zlength (basic_prefix l) -> basic_prefix l = l.
Proof.
  induction l as [|a l IH]; intros H; simpl in *; auto.
  destruct (a <? 128).
  - f_equal. apply IH. rewrite !Zlength_cons in H. lia.
  - rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l). lia.
Qed.

(* A literal octet >= 0x80 makes decode fail. *)
Lemma rbf_literal_fail: forall inp cap i,
  0 <= i < last_delim inp -> 128 <= Znth i inp -> fst (decode inp cap) = false.
Proof.
  intros inp cap i Hi Hn. unfold decode.
  destruct (cap <? last_delim inp); [ reflexivity | ].
  pose proof (DecModel.last_delim_range inp) as Hr. pose proof (Zlength_nonneg inp).
  assert (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <= i).
  { apply rbf_basic_prefix_short; [ rewrite Zlength_sublist by lia; lia | ].
    rewrite Znth_sublist by lia. rewrite Z.add_0_r. exact Hn. }
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp) eqn:E;
    [ reflexivity | apply Z.ltb_ge in E; lia ].
Qed.

Lemma rbf_filter_insert: forall i x l, 0 <= i <= Zlength l -> 128 <= x ->
  filter lt128 (insert_at i x l) = filter lt128 l.
Proof.
  intros i x l Hi Hx. unfold insert_at.
  rewrite filter_app. simpl. unfold lt128 at 2.
  destruct (x <? 128) eqn:E; [ apply Z.ltb_lt in E; lia | ].
  rewrite <- filter_app, <- sublist_split by lia. rewrite sublist_same by lia. reflexivity.
Qed.

(* The main loop only inserts code points >= 128: the basic code points of the output are those it started with. *)
Lemma rbf_steps_filter: forall inp fuel cap pos n i bias out,
  128 <= n -> 0 <= i ->
  filter lt128 (snd (steps inp fuel cap pos n i bias out)) = filter lt128 out.
Proof.
  intros inp fuel. induction fuel; intros cap pos n i bias out Hn Hi; cbn [steps]; [ reflexivity | ].
  destruct (Zlength inp <=? pos); [ reflexivity | ].
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|] eqn:D; [ | reflexivity ].
  assert (0 <= i1) by (eapply ARDecRange.digits_nonneg; [ exact Hi | | exact D ]; lia).
  pose proof (Zlength_nonneg out).
  destruct (maxint <? n + i1 / (Zlength out + 1)); [ reflexivity | ].
  destruct (cap <=? Zlength out); [ reflexivity | ].
  assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
  assert (0 <= i1 mod (Zlength out + 1) < Zlength out + 1) by (apply Z.mod_pos_bound; lia).
  rewrite IHfuel by lia. apply rbf_filter_insert; lia.
Qed.

Lemma rbf_filter_basic_prefix: forall l, filter lt128 (basic_prefix l) = basic_prefix l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (a <? 128) eqn:E; simpl; auto. unfold lt128 at 1. rewrite E. f_equal. exact IH.
Qed.

(* On success, the basic code points of the output, in order, are the literal octets. *)
Lemma rbf_ok_filter: forall inp cap out,
  decode inp cap = (true, out) -> filter lt128 out = sublist 0 (last_delim inp) inp.
Proof.
  intros inp cap out H. unfold decode in H.
  destruct (cap <? last_delim inp); [ discriminate | ].
  pose proof (DecModel.last_delim_range inp) as Hr. pose proof (Zlength_nonneg inp).
  set (b := last_delim inp) in *. clearbody b.
  destruct (Zlength (basic_prefix (sublist 0 b inp)) <? b) eqn:E; [ discriminate | ].
  apply Z.ltb_ge in E.
  assert (Hbp: basic_prefix (sublist 0 b inp) = sublist 0 b inp).
  { apply rbf_basic_prefix_full. rewrite Zlength_sublist by lia. lia. }
  assert (Hf: filter lt128 (sublist 0 b inp) = sublist 0 b inp).
  { rewrite <- Hbp. apply rbf_filter_basic_prefix. }
  rewrite Hbp in H.
  pose proof (rbf_steps_filter inp (length inp) cap (if b =? 0 then 0 else b + 1) 128 0 72 (sublist 0 b inp)) as Hs.
  specialize (Hs ltac:(lia) ltac:(lia)).
  rewrite H in Hs. simpl in Hs. rewrite Hs. exact Hf.
Qed.

(* The step of the harness's second loop: the basic code points among the first j + 1 of the output. *)
Lemma rbf_filter_step: forall out j, 0 <= j < Zlength out ->
  filter lt128 (sublist 0 (j + 1) out) =
  filter lt128 (sublist 0 j out) ++ (if Znth j out <? 128 then [Znth j out] else []).
Proof.
  intros. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite filter_app. reflexivity.
Qed.

(* The check inside the second loop: if out[j] is basic, it is the next literal octet, and there is one left. *)
Lemma rbf_filter_prefix: forall out lit j, filter lt128 out = lit -> 0 <= j < Zlength out -> Znth j out < 128 ->
  let k := Zlength (filter lt128 (sublist 0 j out)) in k < Zlength lit /\ Znth j out = Znth k lit.
Proof.
  intros out lit j Hf Hj Hlt k.
  assert (E: lit = filter lt128 (sublist 0 j out) ++ Znth j out :: filter lt128 (sublist (j + 1) (Zlength out) out)).
  { rewrite <- Hf. rewrite <- (sublist_same 0 (Zlength out) out) at 1 by lia.
    rewrite (sublist_split 0 (j + 1) (Zlength out)) by lia. rewrite filter_app, rbf_filter_step by lia.
    destruct (Znth j out <? 128) eqn:L; [ | apply Z.ltb_ge in L; lia ].
    rewrite <- app_assoc. reflexivity. }
  rewrite E. subst k. split.
  - rewrite Zlength_app, Zlength_cons. pose proof (Zlength_nonneg (filter lt128 (sublist (j + 1) (Zlength out) out))). lia.
  - rewrite Znth_app2 by lia. rewrite Z.sub_diag, Znth_0_cons. reflexivity.
Qed.

(* The literal part, as octets of the input. *)
Lemma rbf_lit_znth: forall inp k, 0 <= k < last_delim inp ->
  Znth k (sublist 0 (last_delim inp) inp) = Znth k inp.
Proof.
  intros. pose proof (DecModel.last_delim_range inp). pose proof (Zlength_nonneg inp).
  rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma rbf_lit_len: forall inp, Zlength (sublist 0 (last_delim inp) inp) = last_delim inp.
Proof. intros. pose proof (DecModel.last_delim_range inp). pose proof (Zlength_nonneg inp). rewrite Zlength_sublist by lia. lia. Qed.
