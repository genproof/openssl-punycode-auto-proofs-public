(* Law rfc_samples: the 19 samples of RFC 3492 7.1 as the harness's constants hold them (read off the initializers of
   the globals encoded, points and decoded of harness/rfc_samples.c, so that they are the program's data), and the
   fact the check needs: Model.decode of each Punycode string into exactly as many code points as the RFC lists
   succeeds with those code points.  Checked by computation. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.harness.rfc_samples.code.

(* The values of the initializers. *)
Definition init_byte (d: init_data) : Z := match d with Init_int8 i => Int.unsigned i | _ => -1 end.
Definition init_word (d: init_data) : Z := match d with Init_int32 i => Int.unsigned i | _ => -1 end.
Definition init_ref (d: init_data) : ident := match d with Init_addrof i _ => i | _ => 1%positive end.

(* The initializer of the global variable i of the harness. *)
Definition gvar_init_of (i: ident) : list init_data :=
  match find (fun d => Pos.eqb (fst d) i) (prog_defs prog) with
  | Some (_, Gvar v) => gvar_init v
  | _ => []
  end.

(* encoded[s] points to the string literal lit_ids[s]; enc s is its octets (before the terminating NUL);
   pts is points[], dec is decoded[]; the code points of sample s start at start s in decoded[]. *)
Definition lit_ids : list ident := map init_ref (gvar_init v_encoded).
Definition lit_init (s: Z) : list init_data := gvar_init_of (Znth s lit_ids).
Definition enc (s: Z) : list Z := map init_byte (removelast (lit_init s)).
Definition pts : list Z := map init_byte (gvar_init v_points).
Definition dec : list Z := map init_word (gvar_init v_decoded).
Definition start (s: Z) : Z := fold_right Z.add 0 (sublist 0 s pts).

(* The decoded code points of sample s. *)
Definition expected (s: Z) : list Z := sublist (start s) (start s + Znth s pts) dec.

Local Open Scope bool_scope.
Definition list_Z_eqb (a b: list Z) : bool := if list_eq_dec Z.eq_dec a b then true else false.

(* What is checked of sample s: the literal ends with its NUL and has no other, its octets are basic (so the
   signed and unsigned views of a char agree), it is not empty (and short), and decode succeeds into points[s] code points with those of
   decoded[]. *)
Definition sample_ok (s: Z) : bool :=
  list_Z_eqb (map init_byte (lit_init s)) (enc s ++ [0]) &&
  forallb (fun b => (0 <? b) && (b <? 128)) (enc s) &&
  (0 <? Zlength (enc s)) && (Zlength (enc s) <? 100) &&
  (let (ok, out) := decode (enc s) (Znth s pts) in ok && list_Z_eqb out (expected s)).

Definition all_ok : bool :=
  (Zlength lit_ids =? 19) && (Zlength pts =? 19) && (Zlength dec =? 355) && (start 19 =? 355) &&
  forallb (fun b => (0 <? b) && (b <? 256)) pts &&
  forallb (fun w => (0 <=? w) && (w <=? Int.max_unsigned)) dec &&
  forallb sample_ok (map Z.of_nat (seq 0 19)).

Lemma all_ok_true : all_ok = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The facts of the check, one by one                                     *)
(* ---------------------------------------------------------------------- *)

Lemma all_ok_parts :
  Zlength lit_ids = 19 /\ Zlength pts = 19 /\ Zlength dec = 355 /\ start 19 = 355 /\
  Forall (fun b => 0 < b < 256) pts /\ Forall (fun w => 0 <= w <= Int.max_unsigned) dec /\
  (forall s, 0 <= s < 19 -> sample_ok s = true).
Proof.
  pose proof all_ok_true as H. unfold all_ok in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Z.eqb_eq in H1, H2, H3, H4.
  split; [ exact H1 | split; [ exact H2 | split; [ exact H3 | split; [ exact H4 | ] ] ] ].
  split; [ | split ].
  - rewrite forallb_forall in H5. apply Forall_forall. intros b Hb. specialize (H5 b Hb).
    rewrite andb_true_iff, !Z.ltb_lt in H5. lia.
  - rewrite forallb_forall in H6. apply Forall_forall. intros b Hb. specialize (H6 b Hb).
    rewrite andb_true_iff, Z.leb_le, Z.leb_le in H6. lia.
  - intros s Hs. rewrite forallb_forall in H7. apply H7.
    replace s with (Z.of_nat (Z.to_nat s)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma Zlength_lit_ids : Zlength lit_ids = 19.
Proof. apply all_ok_parts. Qed.
Lemma Zlength_pts : Zlength pts = 19.
Proof. apply all_ok_parts. Qed.
Lemma Zlength_dec : Zlength dec = 355.
Proof. apply all_ok_parts. Qed.
Lemma start_19 : start 19 = 355.
Proof. apply all_ok_parts. Qed.
Lemma pts_range : Forall (fun b => 0 < b < 256) pts.
Proof. apply all_ok_parts. Qed.
Lemma dec_range : Forall (fun w => 0 <= w <= Int.max_unsigned) dec.
Proof. apply all_ok_parts. Qed.

Lemma Znth_pts_range s : 0 <= s < 19 -> 0 < Znth s pts < 256.
Proof.
  intros Hs. pose proof pts_range as H. rewrite Forall_forall in H. apply H.
  apply Znth_In. rewrite Zlength_pts. lia.
Qed.

Lemma start_succ s : 0 <= s < 19 -> start (s + 1) = start s + Znth s pts.
Proof.
  intros Hs. unfold start. rewrite (sublist_split 0 s (s + 1)) by (rewrite ?Zlength_pts; lia).
  rewrite fold_right_app. rewrite sublist_len_1 by (rewrite Zlength_pts; lia). simpl.
  generalize (sublist 0 s pts). intros l. induction l as [ | a l IH]; simpl; lia.
Qed.

Lemma sum_app (l1 l2: list Z) : fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1; simpl; lia. Qed.

Lemma sum_nonneg (l: list Z) : Forall (fun b => 0 < b < 256) l -> 0 <= fold_right Z.add 0 l.
Proof. induction 1; simpl; lia. Qed.

Lemma start_range s : 0 <= s <= 19 -> 0 <= start s /\ start s + fold_right Z.add 0 (sublist s 19 pts) = 355.
Proof.
  intros Hs. split.
  - apply sum_nonneg. apply Forall_sublist. exact pts_range.
  - rewrite <- start_19. unfold start.
    rewrite (sublist_split 0 s 19) by (rewrite ?Zlength_pts; lia). rewrite sum_app. reflexivity.
Qed.

(* Sample s's code points lie within decoded[]. *)
Lemma start_bound s : 0 <= s < 19 -> 0 <= start s /\ start s + Znth s pts <= 355.
Proof.
  intros Hs. destruct (start_range s) as [H0 H1]; [ lia | ]. split; [ exact H0 | ].
  rewrite (sublist_split s (s + 1) 19) in H1 by (rewrite ?Zlength_pts; lia).
  rewrite sum_app, sublist_len_1 in H1 by (rewrite Zlength_pts; lia). simpl in H1.
  pose proof (sum_nonneg (sublist (s + 1) 19 pts) (Forall_sublist _ _ _ _ pts_range)). lia.
Qed.

(* What decode and the literal of sample s are. *)
Lemma sample_facts s : 0 <= s < 19 ->
  map init_byte (lit_init s) = enc s ++ [0] /\ Forall (fun b => 0 < b < 128) (enc s) /\ 0 < Zlength (enc s) < 100 /\
  decode (enc s) (Znth s pts) = (true, expected s).
Proof.
  intros Hs. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 all_ok_parts))))) s Hs) as H.
  unfold sample_ok in H. destruct (decode (enc s) (Znth s pts)) as [ok out] eqn:E.
  repeat rewrite andb_true_iff in H. destruct H as [[[[H1 H2] H3] H3'] [H4 H5]].
  unfold list_Z_eqb in H1, H5.
  destruct (list_eq_dec Z.eq_dec (map init_byte (lit_init s)) (enc s ++ [0])); [ | discriminate ].
  destruct (list_eq_dec Z.eq_dec out (expected s)); [ | discriminate ]. subst ok out.
  split; [ assumption | split; [ | split; [ apply Z.ltb_lt in H3, H3'; lia | reflexivity ] ] ].
  rewrite forallb_forall in H2. apply Forall_forall. intros b Hb. specialize (H2 b Hb).
  rewrite andb_true_iff, !Z.ltb_lt in H2. lia.
Qed.

Lemma Zlength_expected s : 0 <= s < 19 -> Zlength (expected s) = Znth s pts.
Proof.
  intros Hs. pose proof (start_bound s Hs). pose proof (Znth_pts_range s Hs).
  unfold expected. pose proof Zlength_dec. rewrite Zlength_sublist by lia. lia.
Qed.
