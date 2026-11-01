(* The else-branch of if (t'15) in the main of harness/x_a2ulabel.c: pr_a2ulabel on want (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.

(* The sink record k between the law's compspecs and RefA2u's. *)
Lemma k_cs (buf: val) (c: Z) (p: val):
  @data_at CS Tsh t_sink
    (buf, (Vlong (Int64.repr c), (Vlong (Int64.repr (Int.signed (Int.repr 0))), Vint (Int.repr 0)))) p =
  @data_at OpensslPunycode.proof.harness.RefA2u.CS Tsh OpensslPunycode.proof.harness.RefA2u.t_sink
    (OpensslPunycode.proof.harness.RefA2u.sink_rep buf c ([], false)) p.
Proof.
  unfold OpensslPunycode.proof.harness.RefA2u.sink_rep. simpl.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite CS OpensslPunycode.proof.harness.RefA2u.CS
           (CCE_any CS OpensslPunycode.proof.harness.RefA2u.CS)); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma k_back (v: reptype t_sink) (p: val):
  @data_at OpensslPunycode.proof.harness.RefA2u.CS Tsh OpensslPunycode.proof.harness.RefA2u.t_sink v p
  |-- @data_at_ CS Tsh t_sink p.
Proof.
  eapply derives_trans; [ apply data_at_data_at_ | ].
  rewrite (@data_at__change_composite CS OpensslPunycode.proof.harness.RefA2u.CS
           (CCE_any CS OpensslPunycode.proof.harness.RefA2u.CS)) by reflexivity.
  apply derives_refl.
Qed.

(* The prefix of snap: the string, as pr_a2ulabel wants it. *)
Lemma snap_split (cs2: compspecs) n bs sl p:
  0 <= sl <= n -> Zlength bs = n ->
  @data_at CS Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) p =
  ((if Z.eq_dec sl 0 then @data_at CS Ews (tarray tuchar sl) (vb (sublist 0 sl bs)) p else emp) *
   @arr0 cs2 Ews tuchar (Zlength (sublist 0 sl bs)) (vb (sublist 0 sl bs)) p *
   @data_at CS Ews (tarray tuchar (n + 1 - sl)) (sublist sl (n + 1) (vb (bs ++ [0])))
     (@field_address0 CS (tarray tuchar (n + 1)) (SUB sl) p))%logic.
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar Ews (n + 1) sl) by (unfold vb; list_solve).
  replace (sublist 0 sl (vb (bs ++ [0]))) with (vb (sublist 0 sl bs))
    by (unfold vb; rewrite <- sublist_map, map_app; list_solve).
  rewrite Zlength_sublist by lia. replace (sl - 0) with sl by lia.
  f_equal. unfold arr0. destruct (Z.eq_dec sl 0).
  - rewrite sepcon_emp. auto.
  - rewrite emp_sepcon. apply data_at_tuchar_cs.
Qed.

Lemma want_sink ob outlen p:
  Zlength ob = outlen ->
  data_at Ews (tarray tuchar outlen) (vb ob) p =
  OpensslPunycode.proof.harness.RefA2u.sink_buf Ews p outlen (vb ob) [].
Proof.
  intros. unfold OpensslPunycode.proof.harness.RefA2u.sink_buf. simpl.
  rewrite Zlength_nil, sublist_same by (rewrite ?Zlength_vb; auto).
  apply data_at_tuchar_cs.
Qed.

Lemma cps_cs p:
  data_at_ Ews (tarray tuint 512) p =
  @data_at OpensslPunycode.proof.harness.RefA2u.CS Ews (tarray tuint label_cap) (Zrepeat Vundef 512) p.
Proof.
  rewrite data_at__tarray. apply data_at_tuint_cs.
Qed.

(* A buffer of octet values is the values of a list of octets. *)
Lemma vb_fits sh n (vs: list val) p:
  Forall (fun v => exists i, v = Vint i) vs ->
  data_at sh (tarray tuchar n) vs p |-- !! (exists L, bytes_ok L /\ vs = vb L).
Proof.
  intros HV. eapply derives_trans; [ apply data_at_local_facts | ]. apply prop_derives.
  intros [_ H0]. clear - HV H0.
  rewrite value_fits_eq in H0. simpl in H0. destruct H0 as [_ H0].
  exists (map (fun v => match v with Vint i => Int.unsigned i | _ => 0 end) vs).
  induction vs as [ | v vs IH]; [ split; [ constructor | reflexivity ] | ].
  inv HV. inv H0. destruct (IH H3 H5) as [IH1 IH2].
  destruct H2 as [i ->].
  rewrite value_fits_eq in H4. simpl in H4. unfold tc_val' in H4. simpl in H4.
  specialize (H4 ltac:(discriminate)).
  split.
  - constructor; auto. simpl. pose proof (Int.unsigned_range i). rep_lia.
  - simpl. rewrite <- IH2. f_equal. f_equal. rewrite Int.repr_unsigned. auto.
Qed.

Lemma vb_fits' sh n (vs: list val) p:
  Forall (fun v => exists i, v = Vint i) vs ->
  data_at sh (tarray tuchar n) vs p |-- !! (exists L, bytes_ok L /\ vs = vb L) && data_at sh (tarray tuchar n) vs p.
Proof. intros. apply andp_right; [ apply vb_fits; auto | apply derives_refl ]. Qed.

Lemma vb_ints l: Forall (fun v => exists i, v = Vint i) (vb l).
Proof. unfold vb. rewrite Forall_map. apply Forall_forall. intros. simpl. eauto. Qed.

Lemma snap_merge (cs2: compspecs) n bs sl p:
  0 <= sl <= n -> Zlength bs = n ->
  ((if Z.eq_dec sl 0 then @data_at CS Ews (tarray tuchar sl) (vb (sublist 0 sl bs)) p else emp) *
   @arr0 cs2 Ews tuchar (Zlength (sublist 0 sl bs)) (vb (sublist 0 sl bs)) p *
   @data_at CS Ews (tarray tuchar (n + 1 - sl)) (sublist sl (n + 1) (vb (bs ++ [0])))
     (@field_address0 CS (tarray tuchar (n + 1)) (SUB sl) p))%logic
  |-- @data_at CS Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) p.
Proof. intros. rewrite (snap_split cs2 n bs sl p) by auto. apply derives_refl. Qed.

Lemma piece20e {Espec: OracleKind} gv v_k n bs sl pin psnap pcps outlen out want ob:
  semax Delta_main (pre20e gv v_k n bs sl pin psnap pcps outlen out want ob) S20else
    (overridePost (join21 gv v_k n bs pin psnap outlen out want) main_post).
Proof.
  intros. unfold pre20e, S20else, main_post, Delta_main. abbreviate_semax.
  Intros.
  match goal with H: in_ok _ _ |- _ => destruct H as (Hn & Hbs & Hlen) end.
  match goal with H: sl_ok _ _ _ |- _ => destruct H as (Hsl & Hnz & Hz) end.
  forward. forward. forward. forward.
  assert_PROP (isptr psnap) as Hps by entailer!.
  rewrite (k_cs want outlen v_k).
  rewrite (snap_split OpensslPunycode.proof.harness.RefA2u.CS n bs sl psnap) by lia.
  rewrite (want_sink ob outlen want) by auto.
  rewrite (cps_cs pcps).
  Intros.
  forward_call (Ews, psnap, sublist 0 sl bs, Tsh, v_k, want, outlen, vb ob, Ews, Ews, pcps, Zrepeat Vundef 512).
  { entailer!. simpl. rewrite Zlength_sublist by lia. replace (sl - 0) with sl by lia. reflexivity. }
  { refine (conj _ (conj _ _)).
    - unfold bytes_ok; apply Forall_sublist; auto.
    - rewrite Zlength_sublist by lia; lia.
    - rewrite Zlength_vb; auto. }
  Intros vret.
  forward_call.
  { match goal with E: Int.repr (Z.b2z (Int.eq ?a ?a)) = Int.zero |- _ =>
      rewrite Int.eq_true in E; discriminate E end. }
  sep_apply (snap_merge OpensslPunycode.proof.harness.RefA2u.CS n bs sl psnap ltac:(lia) Hlen).
  sep_apply (k_back (RefA2u.sink_rep want outlen (snd (a2ulabel (sublist 0 sl bs) outlen), fst vret)) v_k).
  unfold OpensslPunycode.proof.harness.RefA2u.sink_buf.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.harness.RefA2u.CS CS).
  sep_apply (vb_fits' Ews outlen (vb (snd (a2ulabel (sublist 0 sl bs) outlen)) ++
     sublist (Zlength (snd (a2ulabel (sublist 0 sl bs) outlen))) outlen (vb ob)) out).
  { apply Forall_app; split; [ apply vb_ints | apply Forall_sublist, vb_ints ]. }
  Intros. match goal with H: exists L, _ |- _ => destruct H as [L [HL HLe]] end.
  rewrite HLe.
  unfold join21. Exists L 0 0. unfold pre21, in_ok, OpensslPunycode.proof.punycode.PunySpec.out_buf, want_buf,
    OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  rewrite !if_false by (try lia; intro X; subst out; contradiction).
  unfold arr0. rewrite if_false by lia.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.punycode.PunySpec.CS CS).
  entailer!.
  match goal with E: Zlength (vb L) = _ |- _ => rewrite Zlength_vb in E; exact E end.
Qed.
