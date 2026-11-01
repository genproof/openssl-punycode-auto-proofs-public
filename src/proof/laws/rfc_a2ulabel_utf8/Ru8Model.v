(* Law rfc_a2ulabel_utf8, the model: for a label "xn--" ++ s (s without '.' and NUL), Model.a2ulabel is the UTF-8
   form of the decoding of s into at most 512 code points, then the NUL, when every code point is at most 0x10FFFF;
   else -1.  ru8_want is what the harness computes in its buffer want (before its NUL). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.

(* The ACE prefix "xn--". *)
Definition xn : list Z := [120; 110; 45; 45].

(* The UTF-8 octets of the decoding of s: none when the decoding fails (also for inputs of 2^32 - 1 octets or more,
   which ossl_punycode_decode rejects) or gives a code point above 0x10FFFF. *)
Definition ru8_want (s: list Z) : option (list Z) :=
  if Int.max_unsigned <=? Zlength s then None else
  match decode s label_cap with
  | (true, cps) => if forallb (fun c => c <=? 1114111) cps then Some (concat (map utf8 cps)) else None
  | (false, _) => None
  end.

(* utf8 c is empty exactly for the code points above 0x10FFFF. *)
Lemma ru8_utf8_nil: forall c, Zlength (utf8 c) =? 0 = negb (c <=? 1114111).
Proof.
  intros c. unfold utf8.
  destruct (c <? 128) eqn:E1; [apply Z.ltb_lt in E1; rewrite (proj2 (Z.leb_le c 1114111)) by lia; reflexivity|].
  destruct (c <? 2048) eqn:E2; [apply Z.ltb_lt in E2; rewrite (proj2 (Z.leb_le c 1114111)) by lia; reflexivity|].
  destruct (c <? 65536) eqn:E3; [apply Z.ltb_lt in E3; rewrite (proj2 (Z.leb_le c 1114111)) by lia; reflexivity|].
  destruct (c <=? 1114111); reflexivity.
Qed.

(* A put never clears the short flag. *)
Lemma ru8_put_short: forall cap k bs, snd k = true -> snd (put cap k bs) = true.
Proof.
  intros cap [acc b] bs H. simpl in H; subst. unfold put.
  destruct (Zlength bs =? 0); [reflexivity|]. destruct (_ <? _); reflexivity.
Qed.

(* The UTF-8 forms of code points none of which is above 0x10FFFF, written from (acc, b): all are written, and the
   sink ends with acc followed by them and its flag unchanged when the flag was clear and they fit, short else. *)
Lemma ru8_put_utf8s: forall cap cps acc b,
  forallb (fun c => c <=? 1114111) cps = true -> Zlength acc <= cap ->
  exists k, put_utf8s cap (acc, b) cps = (true, k) /\
    (if andb (negb b) (Zlength acc + Zlength (concat (map utf8 cps)) <=? cap)
     then k = (acc ++ concat (map utf8 cps), false) else snd k = true).
Proof.
  intros cap cps. induction cps as [|c r IH]; intros acc b H Hacc.
  - simpl. exists (acc, b). split; [reflexivity|]. rewrite app_nil_r, Zlength_nil, Z.add_0_r.
    destruct b; simpl; [reflexivity|]. rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity.
  - simpl in H. apply andb_prop in H. destruct H as [Hc Hr].
    simpl. rewrite ru8_utf8_nil, Hc. simpl.
    assert (NE: Zlength (utf8 c) =? 0 = false) by (rewrite ru8_utf8_nil, Hc; reflexivity).
    unfold put at 1. rewrite NE. simpl fst. simpl snd.
    rewrite Zlength_app.
    pose proof (Zlength_nonneg (utf8 c)). pose proof (Zlength_nonneg (concat (map utf8 r))).
    destruct (cap - Zlength acc <? Zlength (utf8 c)) eqn:Ecap.
    + destruct (IH acc true Hr Hacc) as [k [E Hk]]. exists k. split; [exact E|]. simpl in Hk.
      apply Z.ltb_lt in Ecap. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite andb_false_r. exact Hk.
    + apply Z.ltb_ge in Ecap. destruct (IH (acc ++ utf8 c) b Hr ltac:(rewrite Zlength_app; lia)) as [k [E Hk]]. exists k. split; [exact E|].
      rewrite Zlength_app, <- app_assoc, <- Z.add_assoc in Hk. exact Hk.
Qed.

(* A string without '.' is one label. *)
Lemma ru8_labels_from: forall s cur, Forall (fun c => c <> 46) s -> labels_from s cur = [cur ++ s].
Proof.
  induction s as [|c s IH]; intros cur H; simpl.
  - rewrite app_nil_r; reflexivity.
  - inversion H; subst. rewrite (proj2 (Z.eqb_neq c 46)) by assumption.
    rewrite IH by assumption. rewrite <- app_assoc. reflexivity.
Qed.

(* The law in the model: -1 without a decoding; else 1 and the octets with their NUL when they fit in cap, 0 when
   they do not. *)
Lemma ru8_a2ulabel: forall s cap,
  Forall (fun c => 1 <= c <= 255 /\ c <> 46) s -> 1 <= cap ->
  match ru8_want s with
  | None => fst (a2ulabel (xn ++ s) cap) = -1
  | Some w =>
      if Zlength w + 1 <=? cap then a2ulabel (xn ++ s) cap = (1, w ++ [0])
      else fst (a2ulabel (xn ++ s) cap) = 0
  end.
Proof.
  intros s cap Hs Hcap.
  assert (Hl: labels (xn ++ s) = [xn ++ s]).
  { unfold labels. rewrite ru8_labels_from; [reflexivity|].
    unfold xn. repeat constructor; try discriminate. eapply Forall_impl; [|exact Hs]. simpl; intros; tauto. }
  assert (Hace: is_ace (xn ++ s) = true).
  { unfold is_ace, xn. rewrite Zlength_app. pose proof (Zlength_nonneg s).
    rewrite (proj2 (Z.leb_le _ _)) by (change (Zlength [120; 110; 45; 45]) with 4; lia). reflexivity. }
  assert (Hsub: sublist 4 (Zlength (xn ++ s)) (xn ++ s) = s).
  { unfold xn. rewrite Zlength_app. change (Zlength [120; 110; 45; 45]) with 4.
    rewrite sublist_app2 by (pose proof (Zlength_nonneg s); change (Zlength [120; 110; 45; 45]) with 4; lia).
    change (Zlength [120; 110; 45; 45]) with 4. rewrite Z.sub_diag, Z.add_simpl_l, sublist_same; reflexivity. }
  unfold ru8_want, a2ulabel. rewrite Hl. set (l := xn ++ s) in *. clearbody l.
  simpl a2u_labels. unfold label_step. rewrite Hace, Hsub.
  change maxint with Int.max_unsigned.
  destruct (Int.max_unsigned <=? Zlength s); [reflexivity|].
  destruct (decode s label_cap) as [[|] cps]; [|reflexivity].
  destruct (forallb (fun c => c <=? 1114111) cps) eqn:Hf.
  - destruct (ru8_put_utf8s cap cps [] false Hf ltac:(rewrite Zlength_nil; lia)) as [[acc b] [E Hk]]. rewrite E.
    rewrite Zlength_nil, Z.add_0_l in Hk. simpl in Hk. simpl app in Hk.
    set (w := concat (map utf8 cps)) in *.
    destruct (Zlength w <=? cap) eqn:Hw.
    + inversion Hk; subst acc b. unfold put. simpl. change (Zlength [0]) with 1.
      destruct (Zlength w + 1 <=? cap) eqn:Hw1.
      * apply Z.leb_le in Hw1. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
      * apply Z.leb_gt in Hw1. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    + apply Z.leb_gt in Hw. rewrite (proj2 (Z.leb_gt _ _)) by lia. simpl in Hk; subst b.
      rewrite (ru8_put_short cap (acc, true) [0] eq_refl). reflexivity.
  - (* some code point is above 0x10FFFF: put_utf8s stops there with false *)
    assert (G: forall k, fst (put_utf8s cap k cps) = false).
    { clear -Hf. induction cps as [|c r IH]; intros k; simpl in Hf |- *; [discriminate|].
      rewrite ru8_utf8_nil. destruct (c <=? 1114111); simpl in Hf |- *; [apply IH; exact Hf|reflexivity]. }
    destruct (put_utf8s cap ([], false) cps) as [ok k] eqn:E. specialize (G ([], false)). rewrite E in G.
    simpl in G; subst ok. reflexivity.
Qed.
