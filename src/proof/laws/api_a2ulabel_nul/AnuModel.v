(* Law api_a2ulabel_nul: the fact about the model that the law needs.  When ossl_a2ulabel succeeds on a C string
   (no octet 0), the octets it writes are nonzero octets followed by one NUL, and they fit in the buffer: no label
   octet is 0 (the string has none), '.' is 46, the code points that decode gives are nonzero (the literal ones come
   from the string, the inserted ones are >= 128), so their UTF-8 octets are nonzero, and every write of the
   static WPACKET is done only when it fits. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.

(* A nonzero octet. *)
Definition nz (b: Z) : Prop := 1 <= b <= 255.

(* ---- decode gives nonzero code points ---- *)

Lemma digit_value_nonneg c: 0 <= digit_value c.
Proof.
  unfold digit_value.
  destruct (65 <=? c) eqn:E1; destruct (c <=? 90) eqn:E2; simpl;
    try (apply Z.leb_le in E1; lia);
  destruct (97 <=? c) eqn:E3; destruct (c <=? 122) eqn:E4; simpl;
    try (apply Z.leb_le in E3; lia);
  destruct (48 <=? c) eqn:E5; destruct (c <=? 57) eqn:E6; simpl; try (apply Z.leb_le in E5; lia); lia.
Qed.

Lemma digits_mono inp fuel pos i w k bias i1 pos1:
  0 <= i -> 0 <= w -> digits inp fuel pos i w k bias = Some (i1, pos1) -> 0 <= i1.
Proof.
  revert pos i w k. induction fuel as [ | f IH]; intros pos i w k Hi Hw H; simpl in H; [ discriminate | ].
  destruct (Zlength inp <=? pos); [ discriminate | ].
  set (d := digit_value (Znth pos inp)) in H.
  assert (Hd: 0 <= d) by (subst d; apply digit_value_nonneg).
  destruct (36 <=? d); [ discriminate | ].
  destruct (maxint <? i + d * w); [ discriminate | ].
  destruct (d <? threshold k bias).
  - inversion H; subst. nia.
  - destruct (maxint <? w * (36 - threshold k bias)); [ discriminate | ].
    apply (IH (pos + 1) (i + d * w) (w * (36 - threshold k bias)) (k + 36)); auto; [ nia | ].
    assert (threshold k bias <= 26) by (unfold threshold; destruct (k <=? bias); [ lia | ];
      destruct (bias + 26 <=? k) eqn:E; [ lia | apply Z.leb_gt in E; lia ]).
    nia.
Qed.

Lemma insert_at_forall (P: Z -> Prop) i x l: Forall P l -> P x -> Forall P (insert_at i x l).
Proof.
  intros Hl Hx. unfold insert_at. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; auto. apply Forall_sublist; auto.
Qed.

Lemma steps_pos inp fuel cap pos n i bias out ok out':
  1 <= n -> 0 <= i -> Forall (fun c => 1 <= c) out ->
  steps inp fuel cap pos n i bias out = (ok, out') -> Forall (fun c => 1 <= c) out'.
Proof.
  revert pos n i bias out. induction fuel as [ | f IH]; intros pos n i bias out Hn Hi Ho H; cbn [steps] in H; cbv zeta in H.
  - inversion H; subst; auto.
  - destruct (Zlength inp <=? pos); [ inversion H; subst; auto | ].
    destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1] | ] eqn:Ed;
      [ | inversion H; subst; auto ].
    assert (Hi1: 0 <= i1) by (eapply digits_mono; [ exact Hi | | exact Ed ]; lia).
    assert (Hc: 0 < Zlength out + 1) by (pose proof (Zlength_nonneg out); lia).
    destruct (maxint <? n + i1 / (Zlength out + 1)); [ inversion H; subst; auto | ].
    destruct (cap <=? Zlength out); [ inversion H; subst; auto | ].
    assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
    assert (0 <= i1 mod (Zlength out + 1)) by (apply Z.mod_pos_bound; lia).
    eapply IH; [ | | | exact H ]; [ lia | lia | ].
    apply insert_at_forall; auto. lia.
Qed.

Lemma basic_prefix_forall (P: Z -> Prop) l: Forall P l -> Forall P (basic_prefix l).
Proof.
  induction l as [ | c l IH]; intros H; simpl; auto.
  inversion H; subst. destruct (c <? 128); auto.
Qed.

Lemma decode_pos inp cap ok out:
  Forall (fun c => 1 <= c) inp -> decode inp cap = (ok, out) -> Forall (fun c => 1 <= c) out.
Proof.
  intros Hi H. unfold decode in H.
  assert (Hb: Forall (fun c => 1 <= c) (basic_prefix (sublist 0 (last_delim inp) inp)))
    by (apply basic_prefix_forall, Forall_sublist; auto).
  destruct (cap <? last_delim inp); [ inversion H; subst; auto | ].
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp);
    [ inversion H; subst; auto | ].
  eapply steps_pos; [ | | exact Hb | exact H ]; lia.
Qed.

(* ---- UTF-8 of a nonzero code point ---- *)

Lemma utf8_nz c: 1 <= c -> Forall nz (utf8 c).
Proof.
  intros Hc. unfold utf8, nz.
  destruct (c <? 128) eqn:E1; [ apply Z.ltb_lt in E1; repeat constructor; lia | apply Z.ltb_ge in E1 ].
  assert (forall m, 0 < m -> 0 <= c mod m < m) by (intros; apply Z.mod_pos_bound; lia).
  destruct (c <? 2048) eqn:E2; [ apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2 ].
  { assert (c / 64 < 32) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= c / 64) by (apply Z.div_pos; lia).
    pose proof (H 64 ltac:(lia)). repeat constructor; lia. }
  destruct (c <? 65536) eqn:E3; [ apply Z.ltb_lt in E3 | apply Z.ltb_ge in E3 ].
  { assert (c / 4096 < 16) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= c / 4096) by (apply Z.div_pos; lia).
    pose proof (H 64 ltac:(lia)). pose proof (Z.mod_pos_bound (c / 64) 64 ltac:(lia)).
    repeat constructor; lia. }
  destruct (c <=? 1114111) eqn:E4; [ apply Z.leb_le in E4 | constructor ].
  assert (c / 262144 < 5) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= c / 262144) by (apply Z.div_pos; lia).
  pose proof (H 64 ltac:(lia)). pose proof (Z.mod_pos_bound (c / 64) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (c / 4096) 64 ltac:(lia)).
  repeat constructor; lia.
Qed.

(* ---- the sink: nonzero octets within the capacity ---- *)

Definition sink_ok (cap: Z) (k: sink) : Prop := Forall nz (fst k) /\ Zlength (fst k) <= cap.

Lemma put_ok cap k bs: sink_ok cap k -> Forall nz bs -> sink_ok cap (put cap k bs).
Proof.
  intros [Hk Hl] Hb. unfold put.
  destruct (Zlength bs =? 0); [ split; auto | ].
  destruct (cap - Zlength (fst k) <? Zlength bs) eqn:E; [ split; auto | ].
  apply Z.ltb_ge in E. split; simpl.
  - apply Forall_app; auto.
  - rewrite Zlength_app. lia.
Qed.

Lemma put_utf8s_ok cap k cps: sink_ok cap k -> Forall (fun c => 1 <= c) cps ->
  sink_ok cap (snd (put_utf8s cap k cps)).
Proof.
  revert k. induction cps as [ | c r IH]; intros k Hk Hc; simpl; auto.
  inversion Hc; subst.
  destruct (Zlength (utf8 c) =? 0); simpl; auto.
  apply IH; auto. apply put_ok; auto. apply utf8_nz; auto.
Qed.

Lemma label_step_ok cap k l: sink_ok cap k -> Forall nz l -> sink_ok cap (snd (label_step cap k l)).
Proof.
  intros Hk Hl. unfold label_step.
  destruct (is_ace l); [ | apply put_ok; auto ].
  destruct (maxint <=? Zlength (sublist 4 (Zlength l) l)); simpl; auto.
  destruct (decode (sublist 4 (Zlength l) l) label_cap) as [ok cps] eqn:Ed.
  destruct ok; simpl; auto.
  apply put_utf8s_ok; auto.
  eapply decode_pos; [ | exact Ed ].
  apply Forall_sublist. eapply Forall_impl; [ | exact Hl ]. unfold nz; intros; lia.
Qed.

(* The final NUL: when it is written without the sink being short, the octets are those before it, then 0. *)
Lemma put_nul_ok cap k k1: sink_ok cap k -> put cap k [0] = k1 -> snd k1 = false ->
  exists w', fst k1 = w' ++ [0] /\ Forall nz w' /\ Zlength (fst k1) <= cap.
Proof.
  intros [Hk Hl] <- Hs. unfold put in *. simpl in *.
  change (Zlength [0]) with 1 in *. destruct (cap - Zlength (fst k) <? 1) eqn:E; simpl in Hs; [ discriminate | ].
  apply Z.ltb_ge in E. exists (fst k). simpl. split; [ auto | split; auto ].
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma a2u_labels_nul cap k ls k':
  sink_ok cap k -> Forall (Forall nz) ls -> a2u_labels cap k ls = (1, k') ->
  exists w', fst k' = w' ++ [0] /\ Forall nz w' /\ Zlength (fst k') <= cap.
Proof.
  revert k. induction ls as [ | l ls IH]; intros k Hk Hls H; simpl in H.
  - destruct (snd (put cap k [0])) eqn:Es; inversion H; subst.
    eapply put_nul_ok; eauto.
  - inversion Hls; subst.
    pose proof (label_step_ok cap k l Hk ltac:(auto)) as Hk1.
    destruct (label_step cap k l) as [ok k1]. simpl in Hk1.
    destruct ok; [ | discriminate ].
    destruct ls as [ | l' ls'].
    + destruct (snd (put cap k1 [0])) eqn:Es; inversion H; subst.
      eapply put_nul_ok; eauto.
    + apply (IH (put cap k1 [46])); auto.
      apply put_ok; auto. repeat constructor; unfold nz; lia.
Qed.

(* ---- the labels of a string without NUL ---- *)

Lemma labels_from_nz s cur: Forall nz s -> Forall nz cur -> Forall (Forall nz) (labels_from s cur).
Proof.
  revert cur. induction s as [ | c s IH]; intros cur Hs Hc; simpl; [ constructor; auto | ].
  inversion Hs; subst.
  destruct (c =? 46).
  - constructor; auto.
  - apply IH; auto. apply Forall_app; auto.
Qed.

(* The law's fact: on success, the octets written are nonzero octets then the NUL, at most cap of them. *)
Lemma a2ulabel_nul s cap w:
  Forall nz s -> 0 <= cap -> a2ulabel s cap = (1, w) ->
  exists w', w = w' ++ [0] /\ Forall nz w' /\ Zlength w <= cap.
Proof.
  intros Hs Hc H. unfold a2ulabel in H.
  destruct (a2u_labels cap ([], false) (labels s)) as [r k] eqn:E. inversion H; subst.
  apply (a2u_labels_nul cap ([], false) (labels s) k); auto.
  - split; simpl; [ constructor | rewrite Zlength_nil; lia ].
  - apply labels_from_nz; auto.
Qed.

(* ---- the call of the harness ---- *)

(* The conversion of a list of labels ends with -1, 0 or 1. *)
Lemma a2u_labels_res cap k ls:
  fst (a2u_labels cap k ls) = -1 \/ fst (a2u_labels cap k ls) = 0 \/ fst (a2u_labels cap k ls) = 1.
Proof.
  revert k. induction ls as [ | l ls IH]; intros k; simpl.
  - destruct (snd (put cap k [0])); simpl; auto.
  - destruct (label_step cap k l) as [ok k1]. destruct ok; simpl; auto.
    destruct ls as [ | l' ls'].
    + destruct (snd (put cap k1 [0])); simpl; auto.
    + apply IH.
Qed.

(* The result of ossl_a2ulabel by its specification: -1, 0 or 1. *)
Lemma a2u_outcome_res out cap s init fn zf mf:
  let r := fst (fst (fst (PunySpec.a2u_outcome out cap s init fn zf mf))) in r = 1 \/ r = 0 \/ r = -1.
Proof.
  unfold PunySpec.a2u_outcome.
  destruct (Val.eq out nullval); [ simpl; auto | ].
  destruct (cap =? 0); [ simpl; auto | ].
  destruct (negb (fn =? 0)); [ simpl; auto | ].
  destruct mf; [ simpl; auto | ].
  unfold a2ulabel. pose proof (a2u_labels_res cap ([], false) (labels s)) as H.
  destruct (a2u_labels cap ([], false) (labels s)) as [r k]. simpl in *. lia.
Qed.

(* What ossl_a2ulabel leaves in a buffer out (not NULL) of outlen octets init when it returns 1
   (PunySpec.a2u_outcome): nonzero octets w', the NUL, then the octets of init after them. *)
Lemma a2u_outcome_nul out cap s init fn zf mf:
  out <> nullval -> ShimSpec.str_ok s -> 0 <= cap ->
  fst (fst (fst (PunySpec.a2u_outcome out cap s init fn zf mf))) = 1 ->
  exists w', snd (PunySpec.a2u_outcome out cap s init fn zf mf) =
             vb w' ++ [Vint (Int.repr 0)] ++ sublist (Zlength w' + 1) cap init /\
             Forall nz w' /\ Zlength w' + 1 <= cap.
Proof.
  intros Hout Hs Hc. unfold PunySpec.a2u_outcome.
  destruct (Val.eq out nullval); [ contradiction | ].
  destruct (cap =? 0); [ simpl; discriminate | ].
  destruct (negb (fn =? 0)); [ simpl; discriminate | ].
  destruct mf; [ simpl; discriminate | ].
  destruct (a2ulabel s cap) as [r w] eqn:E. simpl. intros ->.
  assert (Hs': Forall nz s) by (eapply Forall_impl; [ | exact Hs ]; unfold nz; intros; rep_lia).
  destruct (a2ulabel_nul s cap w Hs' Hc E) as [w' [-> [Hw Hl]]].
  exists w'. rewrite Zlength_app, Zlength_cons, Zlength_nil in *. rewrite vb_app. simpl.
  split; [ rewrite <- app_assoc; reflexivity | split; [ auto | lia ] ].
Qed.

(* The position of the first NUL of l (its length when it has none). *)
Fixpoint first0 (l: list Z) : Z :=
  match l with [] => 0 | b :: r => if b =? 0 then 0 else 1 + first0 r end.

Lemma first0_range l: 0 <= first0 l <= Zlength l.
Proof.
  induction l as [ | b r IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (b =? 0); lia.
Qed.

Lemma first0_nz l: Forall (fun b => b <> 0) (sublist 0 (first0 l) l).
Proof.
  induction l as [ | b r IH]; simpl.
  - rewrite sublist_nil'; auto.
  - destruct (b =? 0) eqn:E.
    + rewrite sublist_nil'; auto.
    + pose proof (first0_range r).
      rewrite sublist_0_cons by lia. replace (1 + first0 r - 1) with (first0 r) by lia.
      constructor; auto. apply Z.eqb_neq in E; auto.
Qed.

Lemma first0_at l: Znth (first0 l) (l ++ [0]) = 0.
Proof.
  induction l as [ | b r IH]; simpl; [ reflexivity | ].
  destruct (b =? 0) eqn:E.
  - rewrite Znth_0_cons. apply Z.eqb_eq in E; auto.
  - pose proof (first0_range r). rewrite Znth_pos_cons by lia.
    replace (1 + first0 r - 1) with (first0 r) by lia. exact IH.
Qed.

(* The string of l: its octets before the first NUL (none of them 0, so a C string). *)
Lemma first0_str l: bytes_ok l -> ShimSpec.str_ok (sublist 0 (first0 l) l).
Proof.
  intros Hok. pose proof (first0_nz l) as Hnz. pose proof (first0_range l).
  unfold ShimSpec.str_ok. unfold bytes_ok in Hok.
  apply (Forall_sublist _ 0 (first0 l)) in Hok.
  rewrite Forall_forall in *. intros x Hx. specialize (Hok x Hx). specialize (Hnz x Hx). rep_lia.
Qed.

(* The buffer l ++ [0] = the string with its NUL, then the rest. *)
Lemma first0_split l:
  l ++ [0] = (sublist 0 (first0 l) l ++ [0]) ++ sublist (first0 l + 1) (Zlength l + 1) (l ++ [0]).
Proof.
  pose proof (first0_range l). pose proof (first0_at l) as Hz.
  rewrite <- Hz at 2. list_solve.
Qed.
