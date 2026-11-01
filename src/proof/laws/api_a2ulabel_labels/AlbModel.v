(* Law api_a2ulabel_labels: the facts about the model that the law needs.  The labels of s1 '.' s2 are those of s1
   then those of s2; ossl_a2ulabel converts the labels one by one, so -1 (a label that does not convert) for s1 or
   for s2 gives -1 for s1 '.' s2, and two successful conversions give the conversion of s1 '.' s2 into the sum of
   the capacities: the octets of s1's (without its NUL), a '.', those of s2's with its NUL.  The string the harness
   builds from a buffer is the buffer's octets up to the first NUL (first0). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.A2uModel.

(* ---------------------------------------------------------------------- *)
(* The string of a buffer                                                  *)
(* ---------------------------------------------------------------------- *)

(* The position of the first NUL of l (its length when it has none). *)
Fixpoint first0 (l: list Z) : Z :=
  match l with [] => 0 | b :: r => if b =? 0 then 0 else 1 + first0 r end.

(* The string of l: its octets before the first NUL. *)
Definition str_of (l: list Z) : list Z := sublist 0 (first0 l) l.

Lemma first0_range l: 0 <= first0 l <= Zlength l.
Proof.
  induction l as [ | b r IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (b =? 0); lia.
Qed.

Lemma first0_nz l: Forall (fun b => b <> 0) (str_of l).
Proof.
  unfold str_of. induction l as [ | b r IH]; simpl.
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

(* The string of an octet buffer is a C string. *)
Lemma str_of_ok l: bytes_ok l -> OpensslPunycode.proof.shim.ShimSpec.str_ok (str_of l).
Proof.
  intros Hok. pose proof (first0_nz l) as Hnz. pose proof (first0_range l).
  unfold OpensslPunycode.proof.shim.ShimSpec.str_ok. unfold bytes_ok in Hok. unfold str_of in *.
  apply (Forall_sublist _ 0 (first0 l)) in Hok.
  rewrite Forall_forall in *. intros x Hx. specialize (Hok x Hx). specialize (Hnz x Hx). rep_lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The conversion of s1 '.' s2                                             *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* The labels of s1 '.' s2                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma labels_from_app s1 s2 cur:
  labels_from (s1 ++ 46 :: s2) cur = labels_from s1 cur ++ labels_from s2 [].
Proof.
  revert cur. induction s1 as [ | c s1 IH]; intros cur; simpl.
  - reflexivity.
  - destruct (c =? 46); simpl; rewrite IH; reflexivity.
Qed.

Lemma labels_app s1 s2: labels (s1 ++ [46] ++ s2) = labels s1 ++ labels s2.
Proof. unfold labels. simpl. apply labels_from_app. Qed.

Lemma labels_from_nonnil s cur: labels_from s cur <> [].
Proof.
  revert cur. induction s as [ | c s IH]; intros cur; simpl; [ discriminate | ].
  destruct (c =? 46); [ discriminate | apply IH ].
Qed.

(* Every label holds octets of the string. *)
Lemma labels_from_Forall (P: Z -> Prop) s cur:
  Forall P s -> Forall P cur -> Forall (Forall P) (labels_from s cur).
Proof.
  revert cur. induction s as [ | c s IH]; intros cur Hs Hc; simpl.
  - constructor; auto.
  - inversion Hs; subst. destruct (c =? 46).
    + constructor; auto.
    + apply IH; auto. apply Forall_app; split; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Writes that depend on the room left only through whether they fit      *)
(* ---------------------------------------------------------------------- *)

(* f (a family of writes, indexed by the capacity) writes exactly the octets p: from a sink of at most cap octets
   it leaves at most cap octets, the sink is not short afterwards exactly when it was not and p fits, and then p
   has been appended. *)
Definition exact (f: Z -> sink -> sink) (p: list Z) : Prop :=
  forall cap o sh, Zlength o <= cap ->
    Zlength (fst (f cap (o, sh))) <= cap /\
    (snd (f cap (o, sh)) = false <-> sh = false /\ Zlength o + Zlength p <= cap) /\
    (snd (f cap (o, sh)) = false -> fst (f cap (o, sh)) = o ++ p).

Lemma exact_id: exact (fun _ k => k) [].
Proof.
  intros cap o sh H. simpl. rewrite Zlength_nil. split; [ lia | split ].
  - split; [ intros; split; auto; lia | tauto ].
  - intros. rewrite app_nil_r. reflexivity.
Qed.

Lemma exact_put bs: exact (fun cap k => put cap k bs) bs.
Proof.
  intros cap o sh H. unfold put. simpl.
  destruct (Zlength bs =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. simpl. split; [ lia | split ].
    + split; [ intros; split; auto; lia | tauto ].
    + intros. apply Zlength_nil_inv in E0. subst. rewrite app_nil_r. reflexivity.
  - destruct (cap - Zlength o <? Zlength bs) eqn:E1; simpl.
    + apply Z.ltb_lt in E1. split; [ lia | split ].
      * split; [ discriminate | lia ].
      * discriminate.
    + apply Z.ltb_ge in E1. rewrite Zlength_app. split; [ lia | split ].
      * split; [ intros; split; auto; lia | tauto ].
      * reflexivity.
Qed.

Lemma exact_comp f g p q:
  exact f p -> exact g q -> exact (fun cap k => g cap (f cap k)) (p ++ q).
Proof.
  intros Hf Hg cap o sh H.
  destruct (Hf cap o sh H) as [F1 [F2 F3]].
  destruct (f cap (o, sh)) as [o1 sh1] eqn:Ef. simpl in F1, F2, F3.
  destruct (Hg cap o1 sh1 F1) as [G1 [G2 G3]].
  pose proof (Zlength_nonneg p). pose proof (Zlength_nonneg q).
  rewrite Zlength_app. split; [ exact G1 | split ].
  - rewrite G2. split.
    + intros [Hs Hl]. destruct (proj1 F2 Hs) as [Hs0 Hl0]. rewrite (F3 Hs) in Hl.
      rewrite Zlength_app in Hl. split; auto; lia.
    + intros [Hs Hl]. assert (Hs1: sh1 = false) by (apply F2; split; auto; lia).
      split; auto. rewrite (F3 Hs1), Zlength_app. lia.
  - intros Hs2. rewrite (G3 Hs2). apply G2 in Hs2. destruct Hs2 as [Hs1 _].
    rewrite (F3 Hs1). rewrite app_assoc. reflexivity.
Qed.

Lemma exact_ext f g p: (forall cap k, f cap k = g cap k) -> exact f p -> exact g p.
Proof. intros E H cap o sh Ho. rewrite <- !E. apply H; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* The UTF-8 forms, the labels                                             *)
(* ---------------------------------------------------------------------- *)

Fixpoint u8ok (cps: list Z) : bool :=
  match cps with [] => true | c :: r => negb (Zlength (utf8 c) =? 0) && u8ok r end.
Definition u8piece (cps: list Z) : list Z := concat (map utf8 cps).

Lemma put_utf8s_ok cps cap k: fst (put_utf8s cap k cps) = u8ok cps.
Proof.
  revert k. induction cps as [ | c r IH]; intros k; simpl; [ reflexivity | ].
  destruct (Zlength (utf8 c) =? 0); simpl; auto.
Qed.

Lemma put_utf8s_exact cps: u8ok cps = true -> exact (fun cap k => snd (put_utf8s cap k cps)) (u8piece cps).
Proof.
  induction cps as [ | c r IH]; intros Hok; simpl.
  - apply exact_id.
  - simpl in Hok. destruct (Zlength (utf8 c) =? 0); simpl in Hok; [ discriminate | ].
    unfold u8piece; simpl. fold (u8piece r).
    exact (exact_comp _ _ _ _ (exact_put (utf8 c)) (IH Hok)).
Qed.

(* Whether a label converts, and the octets it gives. *)
Definition lok (l: list Z) : bool :=
  if is_ace l then
    if maxint <=? Zlength (sublist 4 (Zlength l) l) then false else
    match decode (sublist 4 (Zlength l) l) label_cap with (true, cps) => u8ok cps | (false, _) => false end
  else true.
Definition lpiece (l: list Z) : list Z :=
  if is_ace l then
    match decode (sublist 4 (Zlength l) l) label_cap with (true, cps) => u8piece cps | (false, _) => [] end
  else l.

Lemma label_step_ok cap k l: fst (label_step cap k l) = lok l.
Proof.
  unfold label_step, lok. destruct (is_ace l); [ | reflexivity ].
  destruct (maxint <=? _); [ reflexivity | ].
  destruct (decode _ label_cap) as [[|] cps]; [ apply put_utf8s_ok | reflexivity ].
Qed.

Lemma label_step_exact l: lok l = true -> exact (fun cap k => snd (label_step cap k l)) (lpiece l).
Proof.
  unfold lok, lpiece, label_step. destruct (is_ace l).
  - destruct (maxint <=? _); [ discriminate | ].
    destruct (decode _ label_cap) as [[|] cps]; [ apply put_utf8s_exact | discriminate ].
  - intros _. apply exact_put.
Qed.

(* ---------------------------------------------------------------------- *)
(* The labels with their separators                                        *)
(* ---------------------------------------------------------------------- *)

(* The labels, each followed by '.' except the last (no NUL): whether all convert, and the sink. *)
Fixpoint body (cap: Z) (k: sink) (ls: list (list Z)) : bool * sink :=
  match ls with
  | [] => (true, k)
  | l :: ls' =>
    let (ok, k1) := label_step cap k l in
    if ok then match ls' with [] => (true, k1) | _ => body cap (put cap k1 [46]) ls' end
    else (false, k1)
  end.

Fixpoint bpiece (ls: list (list Z)) : list Z :=
  match ls with
  | [] => []
  | l :: ls' => lpiece l ++ match ls' with [] => [] | _ => [46] ++ bpiece ls' end
  end.

Lemma body_ok cap k ls: fst (body cap k ls) = forallb lok ls.
Proof.
  revert k. induction ls as [ | l ls IH]; intros k; simpl; [ reflexivity | ].
  pose proof (label_step_ok cap k l) as E.
  destruct (label_step cap k l) as [ok k1]. simpl in E. subst ok.
  destruct (lok l); simpl; [ | reflexivity ].
  destruct ls as [ | l' ls']; [ reflexivity | apply IH ].
Qed.

Lemma body_exact ls: forallb lok ls = true -> exact (fun cap k => snd (body cap k ls)) (bpiece ls).
Proof.
  induction ls as [ | l ls IH]; intros Hok; simpl.
  - apply exact_id.
  - simpl in Hok. apply andb_prop in Hok. destruct Hok as [Hl Hls].
    assert (E: forall cap k, snd (let (ok, k1) := label_step cap k l in
                 if ok then match ls with [] => (true, k1) | _ => body cap (put cap k1 [46]) ls end
                 else (false, k1)) =
               match ls with [] => snd (label_step cap k l)
               | _ => snd (body cap (put cap (snd (label_step cap k l)) [46]) ls) end).
    { intros cap k. pose proof (label_step_ok cap k l) as E.
      destruct (label_step cap k l) as [ok k1]. simpl in E. subst ok. rewrite Hl.
      destruct ls; reflexivity. }
    apply (exact_ext _ _ _ (fun cap k => eq_sym (E cap k))).
    destruct ls as [ | l' ls'].
    + rewrite app_nil_r. apply label_step_exact; auto.
    + apply (exact_comp (fun cap k => snd (label_step cap k l))
               (fun cap k => snd (body cap (put cap k [46]) (l' :: ls'))) (lpiece l) ([46] ++ bpiece (l' :: ls'))).
      * apply label_step_exact; auto.
      * apply (exact_comp (fun cap k => put cap k [46]) (fun cap k => snd (body cap k (l' :: ls')))).
        -- apply exact_put.
        -- apply IH; auto.
Qed.

Lemma a2u_labels_body cap k ls: ls <> [] ->
  a2u_labels cap k ls =
  let (ok, k1) := body cap k ls in
  if ok then let k2 := put cap k1 [0] in (if snd k2 then 0 else 1, k2) else (-1, k1).
Proof.
  revert k. induction ls as [ | l ls IH]; intros k Hne; [ contradiction | ].
  simpl. destruct (label_step cap k l) as [ok k1]. destruct ok; [ | reflexivity ].
  destruct ls as [ | l' ls']; [ reflexivity | ]. apply IH. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* a2ulabel by the pieces                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma a2ulabel_char s cap: 0 <= cap ->
  (forallb lok (labels s) = false -> fst (a2ulabel s cap) = -1) /\
  (forallb lok (labels s) = true ->
     fst (a2ulabel s cap) <> -1 /\
     (fst (a2ulabel s cap) = 1 <-> Zlength (bpiece (labels s)) + 1 <= cap) /\
     (fst (a2ulabel s cap) = 1 -> snd (a2ulabel s cap) = bpiece (labels s) ++ [0])).
Proof.
  intros Hcap. unfold a2ulabel. rewrite a2u_labels_body by apply labels_from_nonnil.
  pose proof (body_ok cap ([], false) (labels s)) as Eok.
  pose proof (body_exact (labels s)) as Hex.
  destruct (body cap ([], false) (labels s)) as [ok k1] eqn:Eb. simpl in Eok. subst ok.
  split.
  - intros E. rewrite E. reflexivity.
  - intros E. rewrite E.
    pose proof (exact_comp _ _ _ _ (Hex E) (exact_put [0]) cap [] false) as H.
    rewrite Zlength_nil in H. specialize (H Hcap). simpl in H. rewrite Eb in H. simpl in H.
    destruct H as [_ [H2 H3]].
    rewrite Zlength_app, Zlength_cons, Zlength_nil in H2.
    destruct (put cap k1 [0]) as [o2 sh2]. simpl in *.
    split; [ destruct sh2; discriminate | split ].
    + destruct sh2; simpl.
      * split; [ discriminate | intros; assert (true = false) by (apply H2; split; auto; lia); discriminate ].
      * split; [ intros _; destruct (proj1 H2 eq_refl); lia | auto ].
    + destruct sh2; simpl; [ discriminate | ]. intros _. apply H3; auto.
Qed.

(* The result is -1, 0 or 1. *)
Lemma a2ulabel_res s cap: 0 <= cap ->
  fst (a2ulabel s cap) = -1 \/ fst (a2ulabel s cap) = 0 \/ fst (a2ulabel s cap) = 1.
Proof.
  intros Hcap. unfold a2ulabel. rewrite a2u_labels_body by apply labels_from_nonnil.
  destruct (body cap ([], false) (labels s)) as [[|] k1]; simpl; auto.
  destruct (snd (put cap k1 [0])); simpl; auto.
Qed.

Lemma bpiece_app ls1 ls2: ls1 <> [] -> ls2 <> [] -> bpiece (ls1 ++ ls2) = bpiece ls1 ++ [46] ++ bpiece ls2.
Proof.
  intros H1 H2. induction ls1 as [ | l ls IH]; [ contradiction | ].
  simpl. destruct ls as [ | l' ls'].
  - simpl. destruct ls2; [ contradiction | ]. rewrite app_nil_r. reflexivity.
  - change (l' :: ls' ++ ls2) with ((l' :: ls') ++ ls2). rewrite IH by discriminate.
    rewrite <- !app_assoc. reflexivity.
Qed.

(* -1 does not depend on the capacity and propagates from either side. *)
Lemma a2ulabel_join_minus1 s1 s2 c1 c2 c:
  0 <= c1 -> 0 <= c2 -> 0 <= c ->
  fst (a2ulabel s1 c1) = -1 \/ fst (a2ulabel s2 c2) = -1 ->
  fst (a2ulabel (s1 ++ [46] ++ s2) c) = -1.
Proof.
  intros H1 H2 H Hm.
  apply (a2ulabel_char (s1 ++ [46] ++ s2) c H). rewrite labels_app, forallb_app.
  destruct Hm as [Hm | Hm].
  - destruct (forallb lok (labels s1)) eqn:E; [ | reflexivity ].
    exfalso. apply (proj1 (proj2 (a2ulabel_char s1 c1 H1) E)). exact Hm.
  - destruct (forallb lok (labels s2)) eqn:E; [ | apply andb_false_r ].
    exfalso. apply (proj1 (proj2 (a2ulabel_char s2 c2 H2) E)). exact Hm.
Qed.
(* ---------------------------------------------------------------------- *)
(* No NUL in the octets of a conversion of a C string                       *)
(* ---------------------------------------------------------------------- *)

(* The decoder inserts code points n >= 128 into the literal part: when the input has no NUL, no code point of its
   output is 0. *)
Lemma steps_pos inp f cap pos n i bias out:
  1 <= n -> 0 <= i -> Forall (fun c => 1 <= c) out ->
  Forall (fun c => 1 <= c) (snd (steps inp f cap pos n i bias out)).
Proof.
  revert cap pos n i bias out. induction f as [ | f IH]; intros cap pos n i bias out Hn Hi Hout;
    cbn [steps snd]; auto.
  destruct (Zlength inp <=? pos); cbn [snd]; auto.
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1] | ] eqn:D; cbn [snd]; auto.
  pose proof (OpensslPunycode.proof.punycode.A2uModel.a2um_digits_mono _ _ _ _ _ _ _ _ _ D Hi ltac:(lia)) as Hi1.
  pose proof (Zlength_nonneg out) as Hl.
  destruct (maxint <? n + i1 / (Zlength out + 1)); cbn [snd]; auto.
  destruct (cap <=? Zlength out); cbn [snd]; auto.
  assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound i1 (Zlength out + 1) ltac:(lia)).
  apply IH; try lia.
  unfold insert_at. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; [ lia | ]. apply Forall_sublist; auto.
Qed.

Lemma basic_prefix_pos l: Forall (fun c => 1 <= c) l -> Forall (fun c => 1 <= c) (basic_prefix l).
Proof.
  induction l as [ | c l IH]; intros H; simpl; auto.
  inversion H; subst. destruct (c <? 128); auto.
Qed.

Lemma decode_pos inp cap: Forall (fun c => 1 <= c) inp -> Forall (fun c => 1 <= c) (snd (decode inp cap)).
Proof.
  intros H. unfold decode.
  assert (Hb: Forall (fun c => 1 <= c) (basic_prefix (sublist 0 (last_delim inp) inp)))
    by (apply basic_prefix_pos, Forall_sublist, H).
  destruct (cap <? last_delim inp); simpl; auto.
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp); simpl; auto.
  apply steps_pos; auto; lia.
Qed.

Lemma utf8_bytes c: 1 <= c -> Forall (fun b => 1 <= b <= 255) (utf8 c).
Proof.
  intros Hc. unfold utf8.
  destruct (c <? 128) eqn:E1; [ apply Z.ltb_lt in E1; repeat constructor; lia | apply Z.ltb_ge in E1 ].
  pose proof (Z.mod_pos_bound c 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (c / 64) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (c / 4096) 64 ltac:(lia)).
  destruct (c <? 2048) eqn:E2; [ apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2 ].
  { assert (0 <= c / 64 < 32) by (split; [ apply Z.div_pos | apply Z.div_lt_upper_bound ]; lia).
    repeat constructor; lia. }
  destruct (c <? 65536) eqn:E3; [ apply Z.ltb_lt in E3 | apply Z.ltb_ge in E3 ].
  { assert (0 <= c / 4096 < 16) by (split; [ apply Z.div_pos | apply Z.div_lt_upper_bound ]; lia).
    repeat constructor; lia. }
  destruct (c <=? 1114111) eqn:E4; [ apply Z.leb_le in E4 | constructor ].
  assert (0 <= c / 262144 < 5) by (split; [ apply Z.div_pos | apply Z.div_lt_upper_bound ]; lia).
  repeat constructor; lia.
Qed.

Lemma u8piece_bytes cps: Forall (fun c => 1 <= c) cps -> Forall (fun b => 1 <= b <= 255) (u8piece cps).
Proof.
  induction cps as [ | c r IH]; intros H; [ constructor | ].
  inversion H; subst. unfold u8piece; simpl. fold (u8piece r).
  apply Forall_app. split; [ apply utf8_bytes; auto | apply IH; auto ].
Qed.

Lemma lpiece_bytes l: Forall (fun b => 1 <= b <= 255) l -> Forall (fun b => 1 <= b <= 255) (lpiece l).
Proof.
  intros H. unfold lpiece. destruct (is_ace l); auto.
  pose proof (decode_pos (sublist 4 (Zlength l) l) label_cap) as Hd.
  destruct (decode (sublist 4 (Zlength l) l) label_cap) as [[|] cps]; [ | constructor ].
  apply u8piece_bytes. apply Hd. apply Forall_sublist. eapply Forall_impl; [ | exact H ]. simpl; intros; lia.
Qed.

Lemma bpiece_bytes ls:
  Forall (Forall (fun b => 1 <= b <= 255)) ls -> Forall (fun b => 1 <= b <= 255) (bpiece ls).
Proof.
  induction ls as [ | l ls IH]; intros H; [ constructor | ].
  inversion H; subst. simpl. apply Forall_app. split; [ apply lpiece_bytes; auto | ].
  destruct ls; [ constructor | ]. constructor; [ lia | apply IH; auto ].
Qed.

Lemma a2ulabel_one s cap w: OpensslPunycode.proof.shim.ShimSpec.str_ok s -> 0 <= cap ->
  a2ulabel s cap = (1, w) ->
  forallb lok (labels s) = true /\ Zlength (bpiece (labels s)) + 1 <= cap /\ w = bpiece (labels s) ++ [0] /\
  Forall (fun b => 1 <= b <= 255) (bpiece (labels s)).
Proof.
  intros Hs Hcap Ha. destruct (a2ulabel_char s cap Hcap) as [Hf Ht].
  destruct (forallb lok (labels s)) eqn:E.
  - destruct (Ht eq_refl) as [_ [H1 H2]]. rewrite Ha in H1, H2. simpl in H1, H2.
    split; [ reflexivity | split; [ apply H1; reflexivity | split; [ apply H2; reflexivity | ] ] ].
    apply bpiece_bytes. apply labels_from_Forall; [ exact Hs | constructor ].
  - specialize (Hf eq_refl). rewrite Ha in Hf. discriminate.
Qed.

(* Two successful conversions: each output is a run of nonzero octets then the NUL, within its capacity, and the
   conversion of s1 '.' s2 into the sum of the capacities succeeds with the first output without its NUL, a '.',
   then the second output. *)
Lemma a2ulabel_join_one s1 s2 c1 c2 w1 w2:
  OpensslPunycode.proof.shim.ShimSpec.str_ok s1 -> OpensslPunycode.proof.shim.ShimSpec.str_ok s2 ->
  0 <= c1 -> 0 <= c2 ->
  a2ulabel s1 c1 = (1, w1) -> a2ulabel s2 c2 = (1, w2) ->
  exists w1' w2', w1 = w1' ++ [0] /\ w2 = w2' ++ [0] /\
    Forall (fun b => 1 <= b <= 255) w1' /\ Forall (fun b => 1 <= b <= 255) w2' /\
    Zlength w1 <= c1 /\ Zlength w2 <= c2 /\
    a2ulabel (s1 ++ [46] ++ s2) (c1 + c2) = (1, w1' ++ [46] ++ w2).
Proof.
  intros Hs1 Hs2 Hc1 Hc2 Ha1 Ha2.
  destruct (a2ulabel_one s1 c1 w1 Hs1 Hc1 Ha1) as [Ok1 [L1 [W1 B1]]].
  destruct (a2ulabel_one s2 c2 w2 Hs2 Hc2 Ha2) as [Ok2 [L2 [W2 B2]]].
  exists (bpiece (labels s1)), (bpiece (labels s2)).
  subst w1 w2. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  do 6 (split; [ auto; lia | ]).
  assert (Ok: forallb lok (labels (s1 ++ [46] ++ s2)) = true)
    by (rewrite labels_app, forallb_app, Ok1, Ok2; reflexivity).
  assert (Bp: bpiece (labels (s1 ++ [46] ++ s2)) = bpiece (labels s1) ++ [46] ++ bpiece (labels s2))
    by (rewrite labels_app; apply bpiece_app; apply labels_from_nonnil).
  destruct (proj2 (a2ulabel_char (s1 ++ [46] ++ s2) (c1 + c2) ltac:(lia)) Ok) as [_ [H1 H2]].
  rewrite Bp in H1, H2. rewrite !Zlength_app, Zlength_cons, Zlength_nil in H1.
  assert (R: fst (a2ulabel (s1 ++ [46] ++ s2) (c1 + c2)) = 1) by (apply H1; lia).
  specialize (H2 R).
  destruct (a2ulabel (s1 ++ [46] ++ s2) (c1 + c2)) as [r w]. simpl in R, H2. subst r w.
  rewrite <- !app_assoc. reflexivity.
Qed.
