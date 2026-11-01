(* Model facts for the body of pr_encode (BodyEncode.v): prefixes of the output, the minimum code point >= n,
   counts of code points, the digit loop's fuel, bounds of adapt/threshold. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.

Definition cnt_lt (n: Z) (l: list Z) : Z := Zlength (filter (fun c => c <? n) l).
Definition cnt_eq (n: Z) (l: list Z) : Z := Zlength (filter (fun c => c =? n) l).

Definition min_step (n: Z) := fun acc c => if andb (n <=? c) (c <? acc) then c else acc.

(* The rest of the encoding after the pass over l for code point n (the continuation of a round). *)
Definition kont (cps: list Z) (f: nat) (n: Z) (l: list Z) (d bi h b: Z) (out: list Z) : option (list Z) :=
  match enc_pass l n d bi h b out with
  | None => None
  | Some (d1, b1, h1, o1) => enc_rounds cps f (n + 1) (d1 + 1) b1 h1 b o1
  end.

Local Opaque enc_digits adapt.

Lemma enc_pass_prefix: forall l n d bi h b out d1 b1 h1 o1,
  enc_pass l n d bi h b out = Some (d1, b1, h1, o1) -> exists s, o1 = out ++ s.
Proof.
  induction l; simpl; intros.
  - inv H. exists []. rewrite app_nil_r; auto.
  - destruct (a <? n).
    + destruct (maxint <? d + 1); [discriminate|]. eauto.
    + destruct (a =? n).
      * apply IHl in H. destruct H as [s ->]. exists (enc_digits 64 d 36 bi ++ s). rewrite app_assoc; auto.
      * eauto.
Qed.

Lemma enc_pass_h: forall l n d bi h b out d1 b1 h1 o1,
  enc_pass l n d bi h b out = Some (d1, b1, h1, o1) -> h1 = h + cnt_eq n l.
Proof.
  unfold cnt_eq. induction l; simpl; intros.
  - inv H. rewrite Zlength_nil; lia.
  - destruct (a <? n) eqn:E1.
    + destruct (maxint <? d + 1); [discriminate|]. apply IHl in H.
      assert (a =? n = false) by (apply Z.eqb_neq; apply Z.ltb_lt in E1; lia). rewrite H0. auto.
    + destruct (a =? n) eqn:E2.
      * apply IHl in H. rewrite Zlength_cons. lia.
      * eauto.
Qed.

Lemma enc_rounds_prefix: forall cps f n d bi h b out e,
  enc_rounds cps f n d bi h b out = Some e -> exists s, e = out ++ s.
Proof.
  induction f; simpl; intros. discriminate.
  destruct (Zlength cps <=? h). inv H. exists []. rewrite app_nil_r; auto.
  destruct (orb _ _). discriminate.
  destruct (enc_pass _ _ _ _ _ _ _) as [[[[d1 b1] h1] o1]|] eqn:E; [|discriminate].
  apply enc_pass_prefix in E. destruct E as [s1 ->]. apply IHf in H. destruct H as [s2 ->].
  exists (s1 ++ s2). rewrite app_assoc; auto.
Qed.

Lemma kont_prefix: forall cps f n l d bi h b out e,
  kont cps f n l d bi h b out = Some e -> exists s, e = out ++ s.
Proof.
  unfold kont; intros.
  destruct (enc_pass _ _ _ _ _ _ _) as [[[[d1 b1] h1] o1]|] eqn:E; [|discriminate].
  apply enc_pass_prefix in E. destruct E as [s1 ->]. apply enc_rounds_prefix in H. destruct H as [s2 ->].
  exists (s1 ++ s2). rewrite app_assoc; auto.
Qed.

Local Transparent enc_digits adapt.

Lemma enc_digits_nonempty: forall f q k bi, 1 <= Zlength (enc_digits f q k bi).
Proof.
  destruct f; intros; cbn [enc_digits].
  - rewrite Zlength_cons, Zlength_nil; lia.
  - destruct (q <? threshold k bi); rewrite Zlength_cons; [rewrite Zlength_nil; lia|].
    pose proof (Zlength_nonneg (enc_digits f ((q - threshold k bi) / (36 - threshold k bi)) (k + 36) bi)). lia.
Qed.

Lemma fits_false: forall cps ocap,
  (forall e, encode cps = Some e -> ocap < Zlength e) -> encode_fits cps ocap = false.
Proof.
  unfold encode_fits; intros. destruct (encode cps) eqn:E; auto.
  specialize (H l eq_refl). apply Z.leb_gt; lia.
Qed.

Lemma prefix_long: forall (out s e: list Z) x, e = out ++ s -> Zlength out < x -> x <= Zlength e -> True.
Proof. auto. Qed.

(* ---- min_ge ---- *)

Lemma min_fold_props: forall n l acc,
  let r := fold_left (min_step n) l acc in
  (r = acc \/ (In r l /\ n <= r)) /\ r <= acc /\ (forall c, In c l -> n <= c -> r <= c).
Proof.
  intros n l. induction l; simpl; intros.
  - split; auto. split. lia. intros; contradiction.
  - assert (Hs: min_step n acc a = if andb (n <=? a) (a <? acc) then a else acc) by reflexivity.
    rewrite Hs. destruct (andb (n <=? a) (a <? acc)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      specialize (IHl a). simpl in IHl. destruct IHl as [H1 [H2 H3]]. split; [|split].
      * destruct H1 as [-> | [? ?]]; right; auto.
      * lia.
      * intros c [<- | ?] ?; auto.
    + specialize (IHl acc). simpl in IHl. destruct IHl as [H1 [H2 H3]]. split; [|split].
      * destruct H1 as [-> | [? ?]]; auto.
      * lia.
      * intros c [<- | ?] ?; auto. apply andb_false_iff in E. destruct E as [E|E].
        apply Z.leb_gt in E; lia. apply Z.ltb_ge in E. lia.
Qed.

Lemma min_ge_props: forall cps n,
  Forall (fun c => 0 <= c <= maxint) cps -> (exists c, In c cps /\ n <= c) ->
  n <= min_ge cps n <= maxint /\ In (min_ge cps n) cps /\ (forall c, In c cps -> n <= c -> min_ge cps n <= c).
Proof.
  intros cps n Hc [c0 [I0 N0]]. unfold min_ge. fold (min_step n).
  destruct (min_fold_props n cps (maxint + 1)) as [H1 [H2 H3]].
  rewrite Forall_forall in Hc. pose proof (H3 c0 I0 N0). pose proof (Hc c0 I0).
  destruct H1 as [E | [I N]]. rewrite E in H. lia.
  split; [|split]; auto. split; auto. specialize (Hc _ I); lia.
Qed.

Lemma min_ge_le: forall cps n, min_ge cps n <= maxint + 1.
Proof. intros. unfold min_ge. fold (min_step n). destruct (min_fold_props n cps (maxint + 1)) as [_ [H _]]; exact H. Qed.

Lemma min_ge_ge: forall cps n, n <= maxint + 1 -> n <= min_ge cps n.
Proof.
  intros. unfold min_ge. fold (min_step n).
  destruct (min_fold_props n cps (maxint + 1)) as [[E|[_ N]] _]; lia.
Qed.

Lemma min_step_eq: forall n acc c, min_step n acc c = if andb (n <=? c) (c <? acc) then c else acc.
Proof. reflexivity. Qed.

(* ---- counts ---- *)

Lemma cnt_lt_le: forall n l, 0 <= cnt_lt n l <= Zlength l.
Proof.
  unfold cnt_lt. induction l; simpl. rewrite !Zlength_nil; lia.
  destruct (a <? n); rewrite ?Zlength_cons; lia.
Qed.

Lemma cnt_eq_nonneg: forall n l, 0 <= cnt_eq n l.
Proof. intros. apply Zlength_nonneg. Qed.

Lemma cnt_lt_exists: forall n l, cnt_lt n l < Zlength l -> exists c, In c l /\ n <= c.
Proof.
  unfold cnt_lt. induction l; simpl; intros. rewrite !Zlength_nil in H; lia.
  destruct (a <? n) eqn:E.
  - rewrite !Zlength_cons in H. destruct IHl as [c [? ?]]. lia. eauto.
  - exists a. split; auto. apply Z.ltb_ge in E; lia.
Qed.

Lemma cnt_eq_In: forall n l, In n l -> 1 <= cnt_eq n l.
Proof.
  unfold cnt_eq. induction l; simpl; intros. contradiction.
  destruct H as [<- | H].
  - rewrite Z.eqb_refl, Zlength_cons. pose proof (Zlength_nonneg (filter (fun c => c =? a) l)). lia.
  - destruct (a =? n); rewrite ?Zlength_cons; specialize (IHl H); lia.
Qed.

Lemma cnt_round: forall n mm l, n <= mm -> (forall c, In c l -> n <= c -> mm <= c) ->
  cnt_lt (mm + 1) l = cnt_lt n l + cnt_eq mm l.
Proof.
  unfold cnt_lt, cnt_eq. induction l; simpl; intros. rewrite !Zlength_nil; lia.
  specialize (IHl H (fun c Hc => H0 c (or_intror Hc))).
  destruct (Z.lt_ge_cases a n).
  - replace (a <? mm + 1) with true by lia. replace (a <? n) with true by lia. replace (a =? mm) with false by lia.
    rewrite !Zlength_cons; lia.
  - specialize (H0 a (or_introl eq_refl) H1). replace (a <? n) with false by lia.
    destruct (a =? mm) eqn:E.
    + apply Z.eqb_eq in E. replace (a <? mm + 1) with true by lia. rewrite !Zlength_cons; lia.
    + apply Z.eqb_neq in E. replace (a <? mm + 1) with false by lia. lia.
Qed.

Lemma cnt_eq_app: forall n l1 l2, cnt_eq n (l1 ++ l2) = cnt_eq n l1 + cnt_eq n l2.
Proof. intros. unfold cnt_eq. rewrite filter_app, Zlength_app. auto. Qed.

Lemma cnt_eq_one: forall n c, cnt_eq n [c] = if c =? n then 1 else 0.
Proof. intros. unfold cnt_eq. simpl. destruct (c =? n); reflexivity. Qed.

(* ---- digits, threshold, adapt ---- *)

Lemma threshold_range: forall k bi, 1 <= threshold k bi <= 26.
Proof. intros. unfold threshold. destruct (k <=? bi) eqn:E1; [lia|]. destruct (bi + 26 <=? k) eqn:E2; lia. Qed.

Lemma digit_char_range: forall d, 0 <= d < 36 -> 48 <= digit_char d <= 122.
Proof. intros. unfold digit_char. destruct (d <? 26) eqn:E; lia. Qed.

Lemma digit_q_bound: forall f q t, 0 <= q < 10 ^ Z.of_nat (S f) -> 1 <= t <= 26 -> t <= q ->
  0 <= (q - t) / (36 - t) < 10 ^ Z.of_nat f.
Proof.
  intros. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  assert (0 < 10 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia).
  set (P := 10 ^ Z.of_nat f) in *.
  assert (10 * P <= (36 - t) * P) by (apply Z.mul_le_mono_nonneg_r; lia).
  set (Q := (36 - t) * P) in *.
  split. apply Z.div_pos; lia.
  apply Z.div_lt_upper_bound. lia. subst Q. lia.
Qed.

Lemma enc_digits_S: forall f q k bi, threshold k bi <= q ->
  enc_digits (S f) q k bi =
  digit_char (threshold k bi + (q - threshold k bi) mod (36 - threshold k bi))
    :: enc_digits f ((q - threshold k bi) / (36 - threshold k bi)) (k + 36) bi.
Proof. intros. simpl. replace (q <? threshold k bi) with false by lia. auto. Qed.

Lemma enc_digits_last: forall f q k bi, q < threshold k bi -> 0 <= q < 10 ^ Z.of_nat f ->
  enc_digits f q k bi = [digit_char q].
Proof. intros. destruct f; simpl; auto. replace (q <? threshold k bi) with true by lia. auto. Qed.

Lemma maxint_lt_pow: maxint < 10 ^ Z.of_nat 64.
Proof.
  assert (10 ^ 10 <= 10 ^ Z.of_nat 64) by (apply Z.pow_le_mono_r; lia).
  unfold maxint. lia.
Qed.

Lemma adapt_loop_bound: forall f d k, 0 <= d -> 0 <= k -> 0 <= adapt_loop f d k <= k + 36 * Z.of_nat f + 36.
Proof.
  induction f; intros; cbn [adapt_loop]; rewrite ?Nat2Z.inj_succ.
  - assert (0 <= 36 * d / (d + 38) < 36).
    { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; nia. } lia.
  - destruct (455 <? d).
    + assert (0 <= d / 35) by (apply Z.div_pos; lia).
      specialize (IHf (d / 35) (k + 36) H1 ltac:(lia)). lia.
    + assert (0 <= 36 * d / (d + 38) < 36).
      { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; nia. } lia.
Qed.

Lemma adapt_bound: forall d np ft, 0 <= d -> 1 <= np -> 0 <= adapt d np ft <= 2400.
Proof.
  intros. unfold adapt.
  assert (0 <= (if ft then d / 700 else d / 2)) by (destruct ft; apply Z.div_pos; lia).
  set (x := if ft then d / 700 else d / 2) in *.
  assert (0 <= x / np) by (apply Z.div_pos; lia).
  pose proof (adapt_loop_bound 64 (x + x / np) 0 ltac:(lia) ltac:(lia)). change (Z.of_nat 64) with 64 in H3. lia.
Qed.

(* ---- basics ---- *)

Lemma filter_sublist_succ: forall (f: Z -> bool) (l: list Z) j, 0 <= j < Zlength l ->
  filter f (sublist 0 (j + 1) l) = filter f (sublist 0 j l) ++ (if f (Znth j l) then [Znth j l] else []).
Proof.
  intros. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite filter_app. f_equal.
  rewrite sublist_len_1 by lia. simpl. destruct (f (Znth j l)); auto.
Qed.

Lemma filter_prefix: forall (f: Z -> bool) (l: list Z) j, 0 <= j <= Zlength l ->
  filter f l = filter f (sublist 0 j l) ++ filter f (sublist j (Zlength l) l).
Proof.
  intros. rewrite <- filter_app. f_equal. rewrite <- sublist_split by lia. rewrite sublist_same; auto.
Qed.
