(* The body of pr_put (harness/puny_ref.h) under the a2ulabel harness's compspecs. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.

Lemma put_step: forall (w l: list Z) (init: list val) i,
  0 <= i < Zlength l -> Zlength w + Zlength l <= Zlength init ->
  upd_Znth (Zlength w + i) (vb (w ++ sublist 0 i l) ++ sublist (Zlength w + i) (Zlength init) init)
    (Vint (Int.repr (Znth i l))) =
  vb (w ++ sublist 0 (i + 1) l) ++ sublist (Zlength w + (i + 1)) (Zlength init) init.
Proof.
  intros. unfold vb. list_solve.
Qed.

Lemma body_pr_put_proof : semax_body Vprog Gprog_put f_pr_put pr_put_spec.
Proof.
  start_function.
  unfold sink_buf, sink_rep.
  destruct k as [w sh]; simpl fst in *; simpl snd in *.
  subst cap.
  destruct (Z.eq_dec (Zlength l) 0) as [E|E].
  { forward_if.
    { forward. unfold put; rewrite E; simpl. entailer!. }
    { match goal with Hc: Int64.repr _ <> _ |- _ => rewrite E in Hc; contradiction end. } }
  unfold arr0; rewrite if_false by auto.
  assert_PROP (Zlength l <= Int64.max_unsigned).
  { entailer!.
    match goal with Hf: field_compatible (Tarray tuchar (Zlength l) noattr) [] p |- _ =>
      destruct Hf as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction. simpl in Hsz. rewrite Z.max_r in Hsz by rep_lia. rep_lia. }
  forward_if.
  { change Int64.zero with (Int64.repr 0) in *.
    match goal with Hc: Int64.repr (Zlength l) = Int64.repr 0 |- _ =>
      apply repr_inj_unsigned64 in Hc; rep_lia end. }
  forward. forward.
  assert (Esub: Int64.sub (Int64.repr (Zlength init)) (Int64.repr (Zlength w)) = Int64.repr ((Zlength init) - Zlength w)).
  { unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; reflexivity. }
  forward_if.
  { match goal with Hc: Int64.ltu _ _ = true |- _ => rename Hc into Hlt end.
    rewrite Esub in Hlt. unfold Int64.ltu in Hlt. rewrite !Int64.unsigned_repr in Hlt by rep_lia.
    destruct zlt in Hlt; [ | discriminate].
    forward. forward.
    assert (Ep: put (Zlength init) (w, sh) l = (w, true)).
    { unfold put; simpl. rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_lt _ _) l0). reflexivity. }
    rewrite Ep. unfold sink_rep, sink_buf; simpl. entailer!.
    unfold arr0; rewrite if_false by auto. cancel. }
  match goal with Hc: Int64.ltu _ _ = false |- _ => rename Hc into Hlt end.
  rewrite Esub in Hlt. unfold Int64.ltu in Hlt. rewrite !Int64.unsigned_repr in Hlt by rep_lia.
  destruct zlt in Hlt; [ discriminate | ].
  forward_for_simple_bound (Zlength l) (EX j: Z,
    PROP ()
    LOCAL (temp _k pk; temp _p p; temp _m (Vlong (Int64.repr (Zlength l))))
    SEP (data_at shk t_sink (buf, (Vlong (Int64.repr (Zlength init)), (Vlong (Int64.repr (Zlength w)),
           Vint (Int.repr (if sh then 1 else 0))))) pk;
         data_at shb (tarray tuchar (Zlength init)) (vb (w ++ sublist 0 j l) ++ sublist (Zlength w + j) (Zlength init) init) buf;
         data_at shp (tarray tuchar (Zlength l)) (vb l) p))%assert.
  { entailer!. rewrite sublist_nil, app_nil_r. replace (Zlength w + 0) with (Zlength w) by lia. cancel. }
  { forward. forward.
    assert_PROP (Zlength (vb l) = Zlength l) by entailer!.
    assert (Hz: Znth i (vb l) = Vint (Int.repr (Znth i l))).
    { unfold vb; rewrite Znth_map by lia; reflexivity. }
    assert (Hb: 0 <= Znth i l <= Byte.max_unsigned).
    { unfold bytes_ok in H; rewrite Forall_Znth in H. apply H; lia. }
    forward.
    { entailer!. unfold vb; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    match goal with |- context [temp _t'4 ?x] =>
      replace x with (Vint (Int.repr (Znth i l))) by (rewrite <- Hz; reflexivity) end.
    assert (Zlength (vb (w ++ sublist 0 i l)) = Zlength w + i).
    { unfold vb. rewrite Zlength_map, Zlength_app, Zlength_sublist by lia. lia. }
    forward.
    { entailer!. }
    replace (Int.zero_ext 8 (Int.repr (Znth i l))) with (Int.repr (Znth i l))
      by (rewrite zero_ext_inrange; auto; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    rewrite put_step by lia.
    entailer!. }
  forward. forward.
  assert (Ep: put (Zlength init) (w, sh) l = (w ++ l, sh)).
  { unfold put; simpl. rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  rewrite Ep. unfold sink_rep, sink_buf; simpl.
  rewrite sublist_same by lia. rewrite Zlength_app.
  unfold arr0; rewrite if_false by auto.
  entailer!.
  apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl. apply andp_left2.
  apply andp_right; [ apply prop_right; auto | ].
  apply andp_derives; [ | apply derives_refl ]. apply prop_right; unfold liftx; simpl; exact I.
Qed.
