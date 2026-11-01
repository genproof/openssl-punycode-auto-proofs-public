(* Piece 26 of the main of harness/api_a2ulabel_labels.c, its end: when both conversions gave 1 and the scans
   found the lengths u1 = |w1|, u2 = |w2| of the two outputs w1 NUL and w2 NUL, the check
   gp_assert(r == 1 && bytes_eq(out, out1, u1) && out[u1] == '.' && bytes_eq(out + u1 + 1, out2, u2 + 1)) passes:
   out holds w1 '.' w2 NUL (AlbMainP26.v applies it after the scans). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Local Open Scope logic.

Module HS := OpensslPunycode.proof.laws.common.HelperSpec.

(* An array of octets cut after its first k elements: the first k as bytes_eq wants them (arr0, nothing when
   k = 0), the rest at p + k. *)
Lemma alb26_split {cs: compspecs} sh n k (v rest: list val) p:
  0 <= k <= n -> Zlength v = k -> Zlength rest = n - k -> field_compatible (tarray tuchar n) [] p ->
  @data_at cs sh (tarray tuchar n) (v ++ rest) p =
  (@arr0 HS.CS sh tuchar k v p * @data_at cs sh (tarray tuchar (n - k)) rest (offset_val k p))%logic.
Proof.
  intros Hk Hv Hr Hfc. unfold arr0. destruct (Z.eq_dec k 0) as [E | E].
  - rewrite E in *. destruct v as [ | v0 v]; [ | rewrite Zlength_cons in Hv; pose proof (Zlength_nonneg v); lia ].
    rewrite emp_sepcon. simpl app. replace (n - 0) with n by lia.
    destruct p; try (destruct Hfc; contradiction). simpl. rewrite Ptrofs.add_zero. reflexivity.
  - rewrite (split2_data_at_Tarray_app k n sh tuchar v rest p) by auto.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite (data_at_tuchar_cs cs HS.CS). simpl. f_equal. f_equal. f_equal. lia.
Qed.

(* The value after the octets of w (the '.' after the output of s1). *)
Lemma alb26_dot {d: Inhabitant val} (w: list Z) (x: val) (l: list val): @Znth val d (Zlength w) (vb w ++ x :: l) = x.
Proof.
  rewrite app_Znth2 by (rewrite Zlength_vb; lia). rewrite Zlength_vb, Z.sub_diag. reflexivity.
Qed.

(* The check, the statement after the two scans inside `if (r1 == 1 && r2 == 1)`. *)
Definition alb26_chk : statement :=
  ltac:(let x := eval cbv [T26] in T26 in
        lazymatch x with
        | Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?c)))) _)) _ =>
            exact c
        end).

Lemma alb26_check {Espec: OracleKind} gv outlen1 outlen2 (w1' w2': list Z) (R1 R2 R: list val) po1 po2 po:
  1 <= outlen1 <= Int64.max_signed -> 1 <= outlen2 <= Int64.max_signed - outlen1 ->
  Forall (fun b => 1 <= b <= 255) w1' -> Forall (fun b => 1 <= b <= 255) w2' ->
  Zlength w1' + 1 <= outlen1 -> Zlength w2' + 1 <= outlen2 ->
  Zlength R1 = outlen1 - Zlength w1' - 1 -> Zlength R2 = outlen2 - Zlength w2' - 1 ->
  Zlength R = outlen1 + outlen2 - Zlength w1' - Zlength w2' - 2 ->
  semax Delta_main
    (PROP ()
     LOCAL (temp _u2 (Vlong (Int64.repr (Zlength w2'))); temp _u1 (Vlong (Int64.repr (Zlength w1')));
            temp _r (Vint (Int.repr 1));
            temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
            temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
     SEP (data_at Ews (tarray tuchar outlen1) (vb (w1' ++ [0]) ++ R1) po1;
          data_at Ews (tarray tuchar outlen2) (vb (w2' ++ [0]) ++ R2) po2;
          data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) po; TT))
    alb26_chk (normal_ret_assert (PROP () LOCAL () SEP (TT))).
Proof.
  intros H1 H2 F1 F2 L1 L2 HR1 HR2 HR.
  unfold alb26_chk, Delta_main. abbreviate_semax.
  assert (Bw1: bytes_ok w1') by (eapply Forall_impl; [ | exact F1 ]; simpl; intros; rep_lia).
  assert (Bw2: bytes_ok (w2' ++ [0])) by (unfold bytes_ok; rewrite Forall_app; split;
    [ eapply Forall_impl; [ | exact F2 ]; simpl; intros; rep_lia | repeat constructor; rep_lia ]).
  assert_PROP (field_compatible (tarray tuchar (outlen1 + outlen2)) [] po) as FCo by entailer!.
  assert_PROP (field_compatible (tarray tuchar outlen1) [] po1) by entailer!.
  assert_PROP (field_compatible (tarray tuchar outlen2) [] po2) by entailer!.
  replace (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) with (vb w1' ++ (vb (46 :: w2' ++ [0]) ++ R))
    by (rewrite vb_app, app_assoc; reflexivity).
  replace (vb (w1' ++ [0]) ++ R1) with (vb w1' ++ (vb [0] ++ R1))
    by (rewrite vb_app, app_assoc; reflexivity).
  forward_if (temp _t'23 (Vint Int.one)).
  2: { exfalso; congruence. }
  { rewrite (alb26_split Ews (outlen1 + outlen2) (Zlength w1') (vb w1') (vb (46 :: w2' ++ [0]) ++ R) po)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    rewrite (alb26_split Ews outlen1 (Zlength w1') (vb w1') (vb [0] ++ R1) po1)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    Intros.
    forward_call (Ews, po, w1', Ews, po1, w1').
    destruct (list_eq_dec Z.eq_dec w1' w1') as [_ | Hne]; [ | contradiction ].
    gather_SEP (arr0 _ _ _ _ po) (data_at _ _ _ (offset_val _ po)).
    rewrite <- (alb26_split Ews (outlen1 + outlen2) (Zlength w1') (vb w1') (vb (46 :: w2' ++ [0]) ++ R) po)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    gather_SEP (arr0 _ _ _ _ po1) (data_at _ _ _ (offset_val _ po1)).
    rewrite <- (alb26_split Ews outlen1 (Zlength w1') (vb w1') (vb [0] ++ R1) po1)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    forward. entailer!. }
  forward_if (temp _t'25 (Vint Int.one)).
  { forward.
    { entailer!. }
    { entailer!. rewrite alb26_dot. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward. entailer!. rewrite alb26_dot. reflexivity. }
  { discriminate. }
  forward_if (PROP () LOCAL (temp _t'26 (Vint Int.one)) SEP (TT)).
  { replace (vb w1' ++ vb (46 :: w2' ++ [0]) ++ R) with (vb (w1' ++ [46]) ++ (vb (w2' ++ [0]) ++ R))
      by (rewrite vb_app, <- app_assoc; reflexivity).
    rewrite (alb26_split Ews (outlen1 + outlen2) (Zlength w1' + 1) (vb (w1' ++ [46])) (vb (w2' ++ [0]) ++ R) po)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    Intros.
    assert_PROP (field_compatible (tarray tuchar (outlen1 + outlen2 - (Zlength w1' + 1))) []
                   (offset_val (Zlength w1' + 1) po)) by entailer!.
    rewrite (alb26_split Ews (outlen1 + outlen2 - (Zlength w1' + 1)) (Zlength (w2' ++ [0])) (vb (w2' ++ [0])) R
               (offset_val (Zlength w1' + 1) po))
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    rewrite (alb26_split Ews outlen2 (Zlength (w2' ++ [0])) (vb (w2' ++ [0])) R2 po2)
      by (rewrite ?Zlength_app, ?Zlength_vb, ?Zlength_cons, ?Zlength_app; auto; simpl; list_solve).
    Intros.
    forward_call (Ews, offset_val (Zlength w1' + 1) po, w2' ++ [0], Ews, po2, w2' ++ [0]).
    { entailer!. destruct po; try (destruct FCo; contradiction). simpl.
      rewrite Zlength_app. reflexivity. }
    { rewrite Zlength_app. change (Zlength [0]) with 1. rep_lia. }
    destruct (list_eq_dec Z.eq_dec (w2' ++ [0]) (w2' ++ [0])) as [_ | Hne]; [ | contradiction ].
    forward. entailer!. }
  { discriminate. }
  forward_call (Int.one).
  entailer!.
Qed.
