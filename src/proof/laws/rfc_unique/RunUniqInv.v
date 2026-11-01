(* Law rfc_unique, model part 2: a successful run of the main loop of Model.decode is determined by its output.

   The decoder's state is (n, i, cur): the code point n, the insertion state i and the output so far.  Each delta
   inserts n' = n + i'/(c+1) at position p = i' mod (c+1) (c = Zlength cur, i' = i + delta), so n' >= n, and
   p >= i when n' = n.  Hence (RunInv) cur holds no code point above n, and the code points n of cur lie before
   position i; and (run_steps_future) the final output keeps, below every v < n, exactly the code points of cur,
   and its first i code points <= n are those of cur.  Two runs from the same state that end with the same
   output do the same first insertion (first_insertion_unique), hence (n' and p fixed) read the same first
   delta, which has one digit string up to case (RunUniqDigits); by induction they read inputs of the same
   length with the same digit-values (steps_unique, in RunUniqSteps.v).  Plain Coq. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqDigits.
Import ListNotations.
Local Open Scope Z_scope.

(* The code points of l up to v, in order. *)
Definition run_upto (v: Z) (l: list Z) : list Z := filter (fun x => x <=? v) l.

(* The invariant of the decoder's state (n, i, cur). *)
Definition RunInv (n i: Z) (cur: list Z) : Prop :=
  128 <= n /\ 0 <= i <= Zlength cur /\ Forall (fun x => x <= n) cur /\
  (forall j, 0 <= j < Zlength cur -> Znth j cur = n -> j < i).

(* What the rest of a run from the state (n, i, cur) keeps of cur in its final output out. *)
Definition RunFuture (n i: Z) (cur out: list Z) : Prop :=
  (forall v, v < n -> run_upto v out = run_upto v cur) /\
  (forall j, 0 <= j < i -> Znth j (run_upto n out) = Znth j cur).

(* ---- insert_at ---- *)

Lemma run_Zlength_insert: forall p x l, 0 <= p <= Zlength l -> Zlength (insert_at p x l) = Zlength l + 1.
Proof.
  intros. unfold insert_at. rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma run_Znth_insert_lt: forall p x l j, 0 <= j < p -> p <= Zlength l -> Znth j (insert_at p x l) = Znth j l.
Proof.
  intros. unfold insert_at. rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
  rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma run_Znth_insert_eq: forall p x l, 0 <= p <= Zlength l -> Znth p (insert_at p x l) = x.
Proof.
  intros. unfold insert_at. rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. replace (p - (p - 0)) with 0 by lia. apply Znth_0_cons.
Qed.

Lemma run_Znth_insert_gt: forall p x l j, 0 <= p < j -> j <= Zlength l ->
  Znth j (insert_at p x l) = Znth (j - 1) l.
Proof.
  intros. unfold insert_at. rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia.
  replace (j - (p - 0)) with (Z.succ (j - p - 1)) by lia.
  rewrite Znth_pos_cons by lia. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma run_Forall_insert: forall (P: Z -> Prop) p x l, 0 <= p <= Zlength l -> Forall P l -> P x ->
  Forall P (insert_at p x l).
Proof.
  intros. unfold insert_at. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; auto. apply Forall_sublist; auto.
Qed.

Lemma run_upto_insert_gt: forall v p x l, 0 <= p <= Zlength l -> v < x ->
  run_upto v (insert_at p x l) = run_upto v l.
Proof.
  intros. unfold run_upto, insert_at. rewrite filter_app. simpl.
  replace (x <=? v) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite <- filter_app, sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma run_upto_all: forall v l, Forall (fun x => x <= v) l -> run_upto v l = l.
Proof.
  intros v l H. induction H; [reflexivity|].
  unfold run_upto in *; simpl. replace (x <=? v) with true by (symmetry; apply Z.leb_le; lia).
  rewrite IHForall. reflexivity.
Qed.

(* ---- one step of the main loop ---- *)

Lemma run_steps_S: forall inp f cap pos n i bias cur out,
  steps inp (S f) cap pos n i bias cur = (true, out) ->
  (Zlength inp <= pos /\ out = cur) \/
  (pos < Zlength inp /\ exists i1 pos1,
     digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1) /\
     Zlength cur < cap /\
     steps inp f cap pos1 (n + i1 / (Zlength cur + 1)) (i1 mod (Zlength cur + 1) + 1)
       (adapt (i1 - i) (Zlength cur + 1) (i =? 0))
       (insert_at (i1 mod (Zlength cur + 1)) (n + i1 / (Zlength cur + 1)) cur) = (true, out)).
Proof.
  intros. cbn [steps] in H.
  destruct (Zlength inp <=? pos) eqn:El.
  - left. apply Z.leb_le in El. inversion H; auto.
  - right. apply Z.leb_gt in El. split; [exact El|].
    destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|]; [|discriminate].
    destruct (maxint <? n + i1 / (Zlength cur + 1)); [discriminate|].
    destruct (cap <=? Zlength cur) eqn:Ec; [discriminate|]. apply Z.leb_gt in Ec.
    exists i1, pos1. auto.
Qed.

Lemma run_steps_len: forall inp f cap pos n i bias cur b out,
  steps inp f cap pos n i bias cur = (b, out) -> Zlength cur <= Zlength out.
Proof.
  intros inp f. induction f; intros cap pos n i bias cur b out H; cbn [steps] in H.
  - inversion H; lia.
  - destruct (Zlength inp <=? pos); [inversion H; lia|].
    destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|];
      [|inversion H; lia].
    destruct (maxint <? n + i1 / (Zlength cur + 1)); [inversion H; lia|].
    destruct (cap <=? Zlength cur); [inversion H; lia|].
    apply IHf in H. rewrite run_Zlength_insert in H; [lia|].
    pose proof (Z.mod_pos_bound i1 (Zlength cur + 1) ltac:(pose proof (Zlength_nonneg cur); lia)). lia.
Qed.

(* The new state after one insertion: the invariant holds, n does not decrease, and an insertion of the same n
   is at a position >= i. *)
Lemma run_step_inv: forall n i cur i1,
  RunInv n i cur -> i <= i1 ->
  let c := Zlength cur in
  let n1 := n + i1 / (c + 1) in
  let p := i1 mod (c + 1) in
  RunInv n1 (p + 1) (insert_at p n1 cur) /\ n <= n1 /\ 0 <= p <= c /\ (n1 = n -> i <= p).
Proof.
  intros n i cur i1 [Hn [Hi [Hall Hpos]]] Hi1 c n1 p.
  assert (Hc: 0 <= c) by apply Zlength_nonneg.
  assert (Hq: 0 <= i1 / (c + 1)) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound i1 (c + 1) ltac:(lia)) as Hp. fold p in Hp.
  assert (Hsame: n1 = n -> i <= p).
  { intros E. assert (i1 / (c + 1) = 0) by (unfold n1 in E; lia).
    unfold p. rewrite Z.mod_small; [lia|]. split; [lia|].
    destruct (Z_lt_le_dec i1 (c + 1)); [lia|].
    assert (1 <= i1 / (c + 1)) by (apply Z.div_le_lower_bound; lia). lia. }
  split; [|split; [unfold n1; lia|split; [lia|exact Hsame]]].
  split; [unfold n1; lia|].
  rewrite run_Zlength_insert by (unfold c in Hp; lia).
  split; [unfold c in Hp; lia|].
  split.
  - apply run_Forall_insert; [unfold c in Hp; lia| |unfold n1; lia].
    eapply Forall_impl; [|exact Hall]. intros a Ha; simpl in Ha. unfold n1; lia.
  - intros j Hj E.
    destruct (Z_lt_le_dec j p) as [Hjp|Hjp]; [lia|].
    destruct (Z.eq_dec j p) as [->|Hne]; [lia|].
    rewrite run_Znth_insert_gt in E by (unfold c in Hp; lia).
    assert (Hle: Znth (j - 1) cur <= n).
    { eapply Forall_forall in Hall; [exact Hall|]. apply Znth_In. unfold c in Hp; lia. }
    assert (n1 = n) by lia. specialize (Hsame H).
    specialize (Hpos (j - 1) ltac:(unfold c in Hp; lia) ltac:(lia)). lia.
Qed.

(* ---- what the rest of a run keeps ---- *)

Lemma run_steps_future: forall inp f cap pos n i bias cur out,
  RunInv n i cur -> 0 <= pos ->
  steps inp f cap pos n i bias cur = (true, out) -> RunFuture n i cur out.
Proof.
  intros inp f. induction f; intros cap pos n i bias cur out HI Hpos H.
  - cbn [steps] in H. inversion H; subst.
    split; [reflexivity|]. intros j Hj. destruct HI as [_ [_ [Hall _]]]. rewrite run_upto_all by exact Hall.
    reflexivity.
  - apply run_steps_S in H. destruct H as [[_ ->]|[_ [i1 [pos1 [Hd [_ Hs]]]]]].
    + split; [reflexivity|]. intros j Hj. destruct HI as [_ [_ [Hall _]]].
      rewrite run_upto_all by exact Hall. reflexivity.
    + pose proof HI as [Hn [Hi [Hall Hp]]].
      destruct (run_digits_shape inp _ pos i 1 36 bias i1 pos1 ltac:(lia) Hpos Hd) as [[X [HX ->]] Hp1].
      destruct (run_step_inv n i cur (i + 1 * X) HI ltac:(lia)) as [HI1 [Hnn [Hpr Hsame]]].
      set (c := Zlength cur) in *.
      set (n1 := n + (i + 1 * X) / (c + 1)) in *.
      set (p := (i + 1 * X) mod (c + 1)) in *.
      destruct (IHf cap pos1 _ _ _ _ _ HI1 ltac:(lia) Hs) as [Hlow Hfirst].
      split.
      * intros v Hv. rewrite Hlow by lia. apply run_upto_insert_gt; lia.
      * intros j Hj.
        destruct (Z.eq_dec n1 n) as [E|E].
        -- specialize (Hsame E). rewrite <- E. rewrite Hfirst by lia.
           apply run_Znth_insert_lt; lia.
        -- rewrite Hlow by lia. rewrite run_upto_insert_gt by lia. rewrite run_upto_all by exact Hall.
           reflexivity.
Qed.

(* If (nA, pA) came first in the order of (n, p), cur would hold nA at position pA: impossible. *)
Lemma run_first_insertion_order: forall n i cur out nA pA nB pB,
  RunInv n i cur ->
  n <= nA -> 0 <= pA <= Zlength cur -> (nA = n -> i <= pA) ->
  RunFuture nA (pA + 1) (insert_at pA nA cur) out ->
  0 <= pB <= Zlength cur ->
  RunFuture nB (pB + 1) (insert_at pB nB cur) out ->
  (nA < nB \/ (nA = nB /\ pA < pB)) -> False.
Proof.
  intros n i cur out nA pA nB pB HI HnA HpA HsA [_ HfA] HpB [HlB HfB] Hord.
  destruct HI as [Hn [Hi [Hall Hpos]]].
  assert (E1: Znth pA (run_upto nA out) = nA).
  { rewrite HfA by lia. apply run_Znth_insert_eq; lia. }
  assert (E2: Znth pA (run_upto nA out) = Znth pA cur).
  { destruct Hord as [Hord|[-> Hord]].
    - rewrite HlB by lia. rewrite run_upto_insert_gt by lia. rewrite run_upto_all.
      + reflexivity.
      + eapply Forall_impl; [|exact Hall]. intros a Ha; simpl in Ha. lia.
    - rewrite HfB by lia. apply run_Znth_insert_lt; lia. }
  rewrite E1 in E2.
  destruct (Z_lt_le_dec pA (Zlength cur)) as [Hin|Hout].
  - assert (Znth pA cur <= n).
    { eapply Forall_forall in Hall; [exact Hall|]. apply Znth_In; lia. }
    assert (nA = n) by lia.
    specialize (HsA H0). specialize (Hpos pA ltac:(lia) ltac:(congruence)). lia.
  - rewrite Znth_overflow in E2 by lia. compute in E2. lia.
Qed.

(* Two first insertions from the same state into the same final output are the same. *)
Lemma first_insertion_unique: forall n i cur out nA pA nB pB,
  RunInv n i cur ->
  n <= nA -> 0 <= pA <= Zlength cur -> (nA = n -> i <= pA) ->
  RunFuture nA (pA + 1) (insert_at pA nA cur) out ->
  n <= nB -> 0 <= pB <= Zlength cur -> (nB = n -> i <= pB) ->
  RunFuture nB (pB + 1) (insert_at pB nB cur) out ->
  nA = nB /\ pA = pB.
Proof.
  intros n i cur out nA pA nB pB HI HnA HpA HsA HfA HnB HpB HsB HfB.
  destruct (Z.lt_total nA nB) as [H|[H|H]].
  - exfalso. eapply (run_first_insertion_order n i cur out nA pA nB pB); eauto.
  - subst nB. split; [reflexivity|].
    destruct (Z.lt_total pA pB) as [H|[H|H]]; [|exact H|].
    + exfalso. eapply (run_first_insertion_order n i cur out nA pA nA pB); eauto.
    + exfalso. eapply (run_first_insertion_order n i cur out nA pB nA pA); eauto.
  - exfalso. eapply (run_first_insertion_order n i cur out nB pB nA pA); eauto.
Qed.
