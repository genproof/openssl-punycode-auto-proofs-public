(* Law api_a2ulabel_size: the shape of a successful conversion.  When ossl_a2ulabel's model gives 1, the octets
   written are at most cap octets, all bytes, and they end with the only NUL among them: the harness finds the
   number of octets written by scanning for the first NUL. *)
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* Nonzero octets: the octets of a string without its NUL. *)
Definition asz_nz (l: list Z) : Prop := Forall (fun b => 1 <= b <= 255) l.

(* The invariant of the sink along the conversion: at most cap octets written, none of them NUL. *)
Definition asz_sink_ok (cap: Z) (k: sink) : Prop := Zlength (fst k) <= cap /\ asz_nz (fst k).

Lemma asz_put_ok: forall cap k l, asz_sink_ok cap k -> asz_nz l -> asz_sink_ok cap (put cap k l).
Proof.
  intros cap [w sh] l [L B] BL. unfold put, asz_sink_ok, asz_nz in *; simpl in *.
  destruct (Zlength l =? 0); simpl; [auto|].
  destruct (cap - Zlength w <? Zlength l) eqn:E; simpl; [auto|].
  apply Z.ltb_ge in E. split; [rewrite Zlength_app; lia|]. apply Forall_app; auto.
Qed.

(* The final NUL: when its write leaves the sink not short, it was written and fitted. *)
Lemma asz_put_nul: forall cap k, snd (put cap k [0]) = false ->
  fst (put cap k [0]) = fst k ++ [0] /\ Zlength (fst k) + 1 <= cap.
Proof.
  intros cap [w sh]. unfold put; simpl. change (Zlength [0]) with 1.
  destruct (cap - Zlength w <? 1) eqn:E; simpl; [discriminate|].
  apply Z.ltb_ge in E. intros _. split; auto; lia.
Qed.

(* The UTF-8 form of a nonzero code point has no NUL octet. *)
Lemma asz_utf8_nz: forall c, 1 <= c -> asz_nz (utf8 c).
Proof.
  intros c H. unfold utf8, asz_nz.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:?; [|] end;
  repeat match goal with H: (_ <? _) = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end;
  repeat match goal with H: (_ <=? _) = _ |- _ => first [apply Z.leb_le in H | apply Z.leb_gt in H] end;
  repeat constructor.
  all: Z.to_euclidean_division_equations; lia.
Qed.

Lemma asz_put_utf8s_ok: forall cap cps k, asz_sink_ok cap k -> Forall (fun c => 1 <= c) cps ->
  asz_sink_ok cap (snd (put_utf8s cap k cps)).
Proof.
  induction cps; intros k K F; simpl; auto. inversion F; subst.
  destruct (Zlength (utf8 a) =? 0); simpl; auto.
  apply IHcps; auto. apply asz_put_ok; auto. apply asz_utf8_nz; auto.
Qed.

Lemma asz_digit_value_nonneg: forall c, 0 <= digit_value c.
Proof.
  intros c. unfold digit_value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  repeat match goal with H: (_ && _) = true |- _ => apply andb_prop in H; destruct H end;
  repeat match goal with H: (_ <=? _) = true |- _ => apply Z.leb_le in H end; lia.
Qed.

Lemma asz_threshold_le: forall k bias, threshold k bias <= 26.
Proof.
  intros k bias. unfold threshold.
  destruct (k <=? bias) eqn:E1; [lia|].
  destruct (bias + 26 <=? k) eqn:E2; [lia|].
  apply Z.leb_gt in E2. lia.
Qed.

(* The digit loop of one delta only increases i. *)
Lemma asz_digits_mono: forall inp f pos i w k bias i1 pos1,
  digits inp f pos i w k bias = Some (i1, pos1) -> 0 <= i -> 0 <= w -> i <= i1.
Proof.
  intros inp f. induction f as [|f IH]; intros pos i w k bias i1 pos1 H Hi Hw; simpl in H; [discriminate|].
  destruct (Zlength inp <=? pos); [discriminate|].
  pose proof (asz_digit_value_nonneg (Znth pos inp)) as Hd.
  destruct (36 <=? digit_value (Znth pos inp)); [discriminate|].
  destruct (maxint <? i + digit_value (Znth pos inp) * w); [discriminate|].
  destruct (digit_value (Znth pos inp) <? threshold k bias).
  - inversion H; subst. nia.
  - pose proof (asz_threshold_le k bias).
    destruct (maxint <? w * (36 - threshold k bias)); [discriminate|].
    apply IH in H; nia.
Qed.

(* The main loop of the decoder inserts only values of n, which starts at 128 and never decreases: the output keeps
   every code point at least 1 when it starts so. *)
Lemma asz_steps_pos: forall inp f cap pos n i bias out,
  1 <= n -> 0 <= i -> Forall (fun c => 1 <= c) out ->
  Forall (fun c => 1 <= c) (snd (steps inp f cap pos n i bias out)).
Proof.
  intros inp f. induction f as [|f IH]; intros cap pos n i bias out Hn Hi Hout; cbn [steps snd]; auto.
  destruct (Zlength inp <=? pos); cbn [snd]; auto.
  destruct (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias) as [[i1 pos1]|] eqn:D; cbn [snd]; auto.
  pose proof (asz_digits_mono _ _ _ _ _ _ _ _ _ D Hi ltac:(lia)) as Hi1.
  pose proof (Zlength_nonneg out) as Hl.
  destruct (maxint <? n + i1 / (Zlength out + 1)); cbn [snd]; auto.
  destruct (cap <=? Zlength out); cbn [snd]; auto.
  assert (0 <= i1 / (Zlength out + 1)) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound i1 (Zlength out + 1) ltac:(lia)).
  apply IH; try lia. unfold insert_at. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; [lia|]. apply Forall_sublist; auto.
Qed.

Lemma asz_basic_prefix_pos: forall l, Forall (fun c => 1 <= c) l -> Forall (fun c => 1 <= c) (basic_prefix l).
Proof.
  induction l as [|c l IH]; intros H; simpl; auto. inversion H; subst.
  destruct (c <? 128); auto.
Qed.

(* The code points decoded from a label without NUL are all at least 1. *)
Lemma asz_decode_pos: forall inp cap, asz_nz inp -> Forall (fun c => 1 <= c) (snd (decode inp cap)).
Proof.
  intros inp cap OK. unfold decode.
  assert (OK1: Forall (fun c => 1 <= c) inp) by (eapply Forall_impl; [|exact OK]; simpl; intros; lia).
  assert (OK0: Forall (fun c => 1 <= c) (basic_prefix (sublist 0 (last_delim inp) inp))).
  { apply asz_basic_prefix_pos. apply Forall_sublist; auto. }
  destruct (cap <? last_delim inp); simpl; auto.
  destruct (Zlength (basic_prefix (sublist 0 (last_delim inp) inp)) <? last_delim inp); simpl; auto.
  apply asz_steps_pos; auto; lia.
Qed.

Lemma asz_label_step_ok: forall cap k l, asz_sink_ok cap k -> asz_nz l -> asz_sink_ok cap (snd (label_step cap k l)).
Proof.
  intros cap k l K L. unfold label_step.
  destruct (is_ace l); [|simpl; apply asz_put_ok; auto].
  destruct (maxint <=? _); simpl; auto.
  assert (R: asz_nz (sublist 4 (Zlength l) l)) by (apply Forall_sublist; auto).
  pose proof (asz_decode_pos _ label_cap R) as P.
  destruct (decode _ label_cap) as [[|] cps]; simpl in *; auto.
  apply asz_put_utf8s_ok; auto.
Qed.

Lemma asz_labels_from_nz: forall s cur, asz_nz s -> asz_nz cur -> Forall asz_nz (labels_from s cur).
Proof.
  induction s as [|c s IH]; intros cur S C; simpl; [constructor; auto; constructor|].
  inversion S; subst.
  destruct (c =? 46); constructor || idtac.
  - auto.
  - apply IH; auto. constructor.
  - apply IH; auto. apply Forall_app; auto.
Qed.

(* The conversion of the labels: a result 1 leaves the octets of nonzero bytes followed by the NUL, within cap. *)
Lemma asz_a2u_labels_one: forall cap ls k k', asz_sink_ok cap k -> Forall asz_nz ls ->
  a2u_labels cap k ls = (1, k') ->
  Zlength (fst k') <= cap /\ exists w', fst k' = w' ++ [0] /\ asz_nz w'.
Proof.
  intros cap. induction ls as [|l ls IH]; intros k k' K F H; simpl in H.
  - destruct (snd (put cap k [0])) eqn:E; inversion H; subst.
    destruct (asz_put_nul _ _ E) as [E1 E2]. destruct K as [K1 K2].
    rewrite E1, Zlength_app, Zlength_cons, Zlength_nil. split; [lia|]. exists (fst k); auto.
  - inversion F; subst.
    pose proof (asz_label_step_ok cap k l K ltac:(auto)) as K1.
    destruct (label_step cap k l) as [ok k1]. simpl in K1.
    destruct ok; [|discriminate].
    destruct ls as [|l2 ls2].
    + destruct (snd (put cap k1 [0])) eqn:E; inversion H; subst.
      destruct (asz_put_nul _ _ E) as [E1 E2]. destruct K1 as [K2 K3].
      rewrite E1, Zlength_app, Zlength_cons, Zlength_nil. split; [lia|]. exists (fst k1); auto.
    + eapply IH; [| |exact H]; auto. apply asz_put_ok; auto. repeat constructor; lia.
Qed.

Lemma a2ulabel_one_shape s cap w:
  OpensslPunycode.proof.shim.ShimSpec.str_ok s -> 0 <= cap ->
  a2ulabel s cap = (1, w) ->
  Zlength w <= cap /\ exists w', w = w' ++ [0] /\ Forall (fun b => 1 <= b <= 255) w'.
Proof.
  intros S C H. unfold a2ulabel in H.
  destruct (a2u_labels cap ([], false) (labels s)) as [r k] eqn:E. inversion H; subst.
  assert (S': asz_nz s).
  { eapply Forall_impl; [|exact S]. simpl. change Byte.max_unsigned with 255. auto. }
  apply (asz_a2u_labels_one cap (labels s) ([], false) k).
  - split; simpl; [rewrite Zlength_nil; lia | constructor].
  - apply asz_labels_from_nz; auto. constructor.
  - auto.
Qed.
