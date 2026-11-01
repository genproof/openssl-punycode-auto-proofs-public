(* Law rfc_unique, the model fact: RFC 3492 6.2, "there is only one encoded string that can represent a given
   sequence of integers", for Model.decode (plain Coq).

   Two successful decodes into the same output have the same literal part (the code points below 128 of the
   output, in order: every inserted code point is >= 128), hence the same last delimiter and the same start of
   the deltas; from there they read octets with the same digit-values (RunUniqSteps.steps_unique) up to inputs
   of the same length.  Two different octets with the same digit-value are a letter in its two cases. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqStmt.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqInv.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqSteps.
Import ListNotations.
Local Open Scope Z_scope.

(* The last delimiter is 0, or the position of a '-'. *)
Lemma run_last_delim_from: forall l j acc,
  last_delim_from l j acc = acc \/
  (j <= last_delim_from l j acc < j + Zlength l /\ Znth (last_delim_from l j acc - j) l = 45).
Proof.
  induction l as [|c l IH]; intros j acc; simpl; [left; reflexivity|].
  rewrite Zlength_cons.
  destruct (IH (j + 1) (if c =? 45 then j else acc)) as [E|[R E]].
  - rewrite E. destruct (c =? 45) eqn:Ec; [|left; reflexivity].
    right. apply Z.eqb_eq in Ec. pose proof (Zlength_nonneg l).
    split; [lia|]. rewrite Z.sub_diag, Znth_0_cons. exact Ec.
  - right. split; [lia|].
    replace (last_delim_from l (j + 1) (if c =? 45 then j else acc) - j)
      with (Z.succ (last_delim_from l (j + 1) (if c =? 45 then j else acc) - (j + 1))) by lia.
    rewrite Znth_pos_cons by lia.
    replace (Z.succ _ - 1) with (last_delim_from l (j + 1) (if c =? 45 then j else acc) - (j + 1)) by lia.
    exact E.
Qed.

Lemma run_last_delim: forall l,
  last_delim l = 0 \/ (0 < last_delim l < Zlength l /\ Znth (last_delim l) l = 45).
Proof.
  intros l. unfold last_delim. destruct (run_last_delim_from l 0 0) as [E|[R E]]; [left; exact E|].
  destruct (Z.eq_dec (last_delim_from l 0 0) 0) as [E0|E0]; [left; exact E0|].
  right. split; [lia|]. rewrite Z.sub_0_r in E. exact E.
Qed.

(* A prefix of basic code points as long as the list is the list. *)
Lemma run_basic_prefix: forall l,
  Zlength (basic_prefix l) <= Zlength l /\
  (Zlength l <= Zlength (basic_prefix l) -> basic_prefix l = l /\ Forall (fun x => x < 128) l).
Proof.
  induction l as [|c l [IHle IHeq]]; simpl; [split; [lia|auto]|].
  destruct (c <? 128) eqn:Ec.
  - rewrite !Zlength_cons. split; [lia|]. intros H.
    destruct IHeq as [-> Hall]; [lia|]. apply Z.ltb_lt in Ec. auto.
  - rewrite Zlength_cons, Zlength_nil. pose proof (Zlength_nonneg l). split; [lia|]. intros; lia.
Qed.

(* Two different octets with the same digit-value are the two cases of a letter (all pairs of octets). *)
Definition run_case_ok (c1 c2: Z) : bool :=
  negb ((digit_value c1 =? digit_value c2) && (digit_value c1 <? 36) && negb (c1 =? c2)) ||
  ((97 <=? Z.lor c1 32) && (Z.lor c1 32 <=? 122) && (Z.lor c2 32 =? Z.lor c1 32)).

Lemma run_case_all:
  forallb (fun a => forallb (fun b => run_case_ok (Z.of_nat a) (Z.of_nat b)) (seq 0 256)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma run_case: forall c1 c2, 0 <= c1 <= 255 -> 0 <= c2 <= 255 ->
  digit_value c1 = digit_value c2 -> digit_value c1 < 36 -> c1 <> c2 ->
  97 <= Z.lor c1 32 <= 122 /\ Z.lor c2 32 = Z.lor c1 32.
Proof.
  intros c1 c2 H1 H2 Hd H36 Hne.
  pose proof run_case_all as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c1) ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H (Z.to_nat c2) ltac:(apply in_seq; lia)). rewrite !Z2Nat.id in H by lia.
  unfold run_case_ok in H.
  rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.ltb_lt _ _) H36), (proj2 (Z.eqb_neq _ _) Hne) in H.
  simpl in H. rewrite !andb_true_iff, Z.leb_le, Z.leb_le, Z.eqb_eq in H. lia.
Qed.

(* What a successful decode gives: the literal part (basic, the octets before the last delimiter, with the
   '-' after it when it is not 0), and a successful main loop from the start of the deltas. *)
Lemma run_decode_ok: forall inp cap out,
  decode inp cap = (true, out) ->
  let b := last_delim inp in
  let bp := sublist 0 b inp in
  0 <= b <= Zlength inp /\ Forall (fun x => x < 128) bp /\ Zlength bp = b /\
  (b = 0 \/ (b < Zlength inp /\ Znth b inp = 45)) /\
  steps inp (length inp) cap (if b =? 0 then 0 else b + 1) 128 0 72 bp = (true, out).
Proof.
  intros inp cap out D b bp. unfold decode in D. fold b in D.
  assert (Hb: b = 0 \/ (0 < b < Zlength inp /\ Znth b inp = 45)) by apply run_last_delim.
  assert (Hr: 0 <= b <= Zlength inp) by (pose proof (Zlength_nonneg inp); lia).
  assert (Hl: Zlength bp = b) by (unfold bp; rewrite Zlength_sublist; lia).
  destruct (cap <? b); [discriminate|].
  fold bp in D.
  destruct (run_basic_prefix bp) as [Hle Heq].
  destruct (Zlength (basic_prefix bp) <? b) eqn:Ebp; [discriminate|]. apply Z.ltb_ge in Ebp.
  destruct Heq as [Ebp' Hall]; [lia|]. rewrite Ebp' in D.
  split; [exact Hr|]. split; [exact Hall|]. split; [exact Hl|]. split; [lia|exact D].
Qed.

Lemma unique_proved : unique_stmt.
Proof.
  intros inp1 inp2 cap out Hb1 Hb2 D1 D2.
  apply run_decode_ok in D1. apply run_decode_ok in D2.
  set (b1 := last_delim inp1) in *. set (b2 := last_delim inp2) in *.
  destruct D1 as [Hr1 [Hall1 [Hl1 [Hd1 S1]]]]. destruct D2 as [Hr2 [Hall2 [Hl2 [Hd2 S2]]]].
  (* The state before the deltas satisfies the invariant. *)
  assert (Hinv: forall bp, Forall (fun x => x < 128) bp -> RunInv 128 0 bp).
  { intros bp Hall. split; [lia|]. pose proof (Zlength_nonneg bp). split; [lia|]. split.
    - eapply Forall_impl; [|exact Hall]. intros a Ha; simpl in Ha; lia.
    - intros j Hj E. eapply Forall_forall in Hall; [|apply Znth_In; exact Hj]. simpl in Hall. lia. }
  (* The literal parts are the code points below 128 of the output. *)
  assert (Hlit: forall bp inp pos, Forall (fun x => x < 128) bp -> 0 <= pos ->
            steps inp (length inp) cap pos 128 0 72 bp = (true, out) -> run_upto 127 out = bp).
  { intros bp inp pos Hall Hpos Hs.
    destruct (run_steps_future _ _ _ _ _ _ _ _ _ (Hinv bp Hall) Hpos Hs) as [Hlow _].
    rewrite Hlow by lia. apply run_upto_all. eapply Forall_impl; [|exact Hall]. intros a Ha; simpl in Ha; lia. }
  assert (Hpos: forall b, 0 <= b -> 0 <= if b =? 0 then 0 else b + 1) by (intros b Hb; destruct (b =? 0); lia).
  pose proof (Hlit _ _ _ Hall1 (Hpos b1 ltac:(lia)) S1) as L1.
  pose proof (Hlit _ _ _ Hall2 (Hpos b2 ltac:(lia)) S2) as L2.
  rewrite L1 in L2. clear L1.
  assert (Eb: b1 = b2) by (rewrite <- Hl1, <- Hl2, L2; reflexivity).
  rewrite <- Eb in S2, Hd2, L2.
  rewrite <- L2 in S2.
  set (pos := if b1 =? 0 then 0 else b1 + 1) in *.
  assert (Hp: 0 <= pos) by (apply Hpos; lia).
  assert (HpA: pos <= Zlength inp1) by (unfold pos; destruct (b1 =? 0) eqn:E; [|apply Z.eqb_neq in E]; lia).
  assert (HpB: pos <= Zlength inp2) by (unfold pos; destruct (b1 =? 0) eqn:E; [|apply Z.eqb_neq in E]; lia).
  destruct (steps_unique (length inp1) inp1 (length inp2) inp2 cap pos 128 0 72 _ out (Hinv _ Hall1) Hp HpA HpB
              ltac:(rewrite Zlength_correct; lia) ltac:(rewrite Zlength_correct; lia) S1 S2) as [Hlen Hdig].
  split; [exact Hlen|].
  intros j Hj Hne.
  assert (Hbyte: forall inp, bytes_ok inp -> 0 <= j < Zlength inp -> 0 <= Znth j inp <= 255).
  { intros inp Hb Hj'. eapply Forall_forall in Hb; [|apply Znth_In; exact Hj']. exact Hb. }
  destruct (Z_lt_le_dec j b1) as [Hjb|Hjb].
  - (* in the literal part: the same octets *)
    exfalso. apply Hne.
    assert (E: Znth j (sublist 0 b1 inp1) = Znth j (sublist 0 b1 inp2)) by (rewrite L2; reflexivity).
    rewrite !Znth_sublist in E by lia. rewrite !Z.add_0_r in E. exact E.
  - destruct (Z.eq_dec j b1) as [Ej|Ej].
    + (* the last delimiter, when it is not 0: '-' in both *)
      destruct (Z.eq_dec b1 0) as [Hz|Hz].
      * split; [right; exact Hz|].
        assert (pos = 0) by (unfold pos; rewrite Hz; reflexivity).
        destruct (Hdig j ltac:(lia)) as [Hv H36].
        apply run_case; auto; apply Hbyte; auto; lia.
      * exfalso. apply Hne.
        destruct Hd1 as [?|[_ E1]]; [lia|]. destruct Hd2 as [?|[_ E2]]; [lia|].
        subst j. congruence.
    + (* among the deltas *)
      split.
      * destruct (Z.eq_dec b1 0) as [Hz|Hz]; [right; exact Hz|left; lia].
      * assert (pos <= j) by (unfold pos; destruct (b1 =? 0) eqn:E; [|apply Z.eqb_neq in E]; lia).
        destruct (Hdig j ltac:(lia)) as [Hv H36].
        apply run_case; auto; apply Hbyte; auto; lia.
Qed.
