(* Piece 26 of the main of harness/api_a2ulabel_labels.c: when both conversions give 1, the lengths u1, u2 of their
   outputs and the check of the output for s1 '.' s2 (AlbP26Chk.v), then the return (AlbMainDefs). *)
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
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbP26Chk.
Local Open Scope logic.

(* The result of the model's ossl_a2ulabel is -1, 0 or 1 (so the int tests r1 == 1 etc. decide r1 = 1). *)
Lemma alb26_labels_range cap ls: forall k, -1 <= fst (a2u_labels cap k ls) <= 1.
Proof.
  induction ls as [ | l ls IH]; intros k; simpl.
  - destruct (snd (put cap k [0])); simpl; lia.
  - destruct (label_step cap k l) as [ok k1]. destruct ok.
    + destruct ls as [ | l' ls']; [ simpl; destruct (snd (put cap k1 [0])); simpl; lia | apply IH ].
    + simpl; lia.
Qed.

Lemma alb26_range s cap: -1 <= fst (a2ulabel s cap) <= 1.
Proof.
  unfold a2ulabel. pose proof (alb26_labels_range cap (labels s) ([], false)).
  destruct (a2u_labels cap ([], false) (labels s)). simpl in *. lia.
Qed.

(* The octet u of an output w NUL followed by other values: the NUL at u = |w|, a nonzero octet before. *)
Lemma alb26_znth (w: list Z) (R: list val) u:
  0 <= u <= Zlength w -> Znth u (vb (w ++ [0]) ++ R) = Vint (Int.repr (Znth u (w ++ [0]))).
Proof.
  intros Hu. rewrite app_Znth1 by (rewrite Zlength_vb, Zlength_app; list_solve).
  unfold vb. rewrite Znth_map by list_solve. reflexivity.
Qed.

Lemma alb26_nz (w: list Z) u:
  Forall (fun b => 1 <= b <= 255) w -> 0 <= u <= Zlength w ->
  (u = Zlength w /\ Znth u (w ++ [0]) = 0) \/ (u < Zlength w /\ 1 <= Znth u (w ++ [0]) <= 255).
Proof.
  intros Hw Hu. destruct (Z.eq_dec u (Zlength w)) as [E | E].
  - left. split; auto. rewrite app_Znth2 by lia. rewrite E, Z.sub_diag. reflexivity.
  - right. split; [ lia | ]. rewrite app_Znth1 by lia. eapply Forall_Znth in Hw; [ exact Hw | lia ].
Qed.

Lemma piece26 : join_one_stmt -> piece26_stmt.
Proof.
  intros Hjoin Espec gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po.
  unfold pre25, T26, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  unfold outbuf.
  pose proof (alb26_range t1 outlen1). pose proof (alb26_range t2 outlen2).
  destruct (a2ulabel t1 outlen1) as [r1 w1] eqn:E1.
  destruct (a2ulabel t2 outlen2) as [r2 w2] eqn:E2.
  simpl fst in *. simpl snd in *.
  assert (Hc: (r1 = 1 /\ r2 = 1) \/ ~(r1 = 1 /\ r2 = 1)) by lia.
  destruct Hc as [[-> ->] | Hc].
  2: {
    (* r1 <> 1 or r2 <> 1: the check is skipped. *)
    forward_if (temp _t'28 (Vint (Int.repr 0))).
    { forward. entailer!. assert (r2 = -1 \/ r2 = 0) as [-> | ->] by lia;
      reflexivity. }
    { forward. entailer!. }
    forward_if (PROP () LOCAL () SEP (TT)).
    { contradiction. }
    { forward. entailer!. }
    forward. Exists (Int.repr 0). entailer!. }
  (* r1 = r2 = 1: the outputs are w1' NUL and w2' NUL, the output for s1 '.' s2 is w1' '.' w2' NUL. *)
  destruct (Hjoin t1 t2 outlen1 outlen2 w1 w2 H H0 ltac:(lia) ltac:(lia) E1 E2)
    as [w1' [w2' [-> [-> [F1 [F2 [L1 [L2 E3]]]]]]]].
  simpl app in E3. rewrite E3. simpl fst. simpl snd.
  forward_if (temp _t'28 (Vint Int.one)).
  { forward. entailer!. }
  { contradiction. }
  forward_if (PROP () LOCAL () SEP (TT)).
  2: { discriminate. }
  2: { forward. Exists (Int.repr 0). entailer!. }
  assert (Zlength (vb ob1) = outlen1) by (rewrite Zlength_vb; auto).
  assert (Zlength (vb ob2) = outlen2) by (rewrite Zlength_vb; auto).
  assert (Zlength (vb ob) = outlen1 + outlen2) by (rewrite Zlength_vb; auto).
  set (R1 := sublist (Zlength (w1' ++ [0])) outlen1 (vb ob1)).
  set (R2 := sublist (Zlength (w2' ++ [0])) outlen2 (vb ob2)).
  set (R := sublist (Zlength (w1' ++ 46 :: w2' ++ [0])) (outlen1 + outlen2) (vb ob)).
  assert (HR1: Zlength R1 = outlen1 - Zlength w1' - 1) by (subst R1; rewrite Zlength_sublist; list_solve).
  assert (HR2: Zlength R2 = outlen2 - Zlength w2' - 1) by (subst R2; rewrite Zlength_sublist; list_solve).
  assert (HR: Zlength R = outlen1 + outlen2 - Zlength w1' - Zlength w2' - 2)
    by (subst R; rewrite Zlength_sublist; list_solve).
  clearbody R1 R2 R.
  rewrite Zlength_app in L1, L2. change (Zlength [0]) with 1 in L1, L2.
  forward. forward.
  (* while (u1 < outlen1 && out1[u1] != 0) u1++; *)
  forward_loop (EX u: Z,
    PROP (0 <= u <= Zlength w1')
    LOCAL (temp _u2 (Vlong (Int64.repr 0)); temp _u1 (Vlong (Int64.repr u)); temp _r (Vint (Int.repr 1));
           temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
           temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
    SEP (data_at Ews (tarray tuchar outlen1) (vb (w1' ++ [0]) ++ R1) po1;
         data_at Ews (tarray tuchar outlen2) (vb (w2' ++ [0]) ++ R2) po2;
         data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) po; TT))
  break: (
    PROP ()
    LOCAL (temp _u2 (Vlong (Int64.repr 0)); temp _u1 (Vlong (Int64.repr (Zlength w1')));
           temp _r (Vint (Int.repr 1));
           temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
           temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
    SEP (data_at Ews (tarray tuchar outlen1) (vb (w1' ++ [0]) ++ R1) po1;
         data_at Ews (tarray tuchar outlen2) (vb (w2' ++ [0]) ++ R2) po2;
         data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) po; TT)).
  { Exists 0. entailer!. }
  { Intros u.
    pose proof (alb26_nz w1' u F1 ltac:(lia)) as Hnz.
    assert (Hb: 0 <= Znth u (w1' ++ [0]) <= 255) by (destruct Hnz; lia).
    forward_if (temp _t'21 (Vint (Int.repr (if zeq u (Zlength w1') then 0 else 1)))).
    { forward.
      { entailer!. rewrite alb26_znth by lia. simpl.
        rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward. entailer!. rewrite alb26_znth by lia.
      destruct Hnz as [[Hu Hz] | [Hlt Hb']].
      { rewrite Hz. destruct (zeq u (Zlength w1')); [ reflexivity | lia ]. }
      rewrite zeq_false by lia. simpl. unfold Int.eq.
      rewrite (Int.unsigned_repr (Znth u (w1' ++ [0]))) by rep_lia.
      destruct (zeq (Znth u (w1' ++ [0])) (Int.unsigned (Int.repr 0))) as [E|E];
        [ rewrite Int.unsigned_repr in E by rep_lia; lia | reflexivity ]. }
    { exfalso; lia. }
    forward_if.
    { destruct (zeq u (Zlength w1')); [ contradiction | ].
      forward. Exists (u + 1). entailer!. }
    { destruct (zeq u (Zlength w1')) as [Hu | ]; [ | discriminate ].
      forward. rewrite Hu. entailer!. } }
  (* while (u2 < outlen2 && out2[u2] != 0) u2++; *)
  forward_loop (EX u: Z,
    PROP (0 <= u <= Zlength w2')
    LOCAL (temp _u2 (Vlong (Int64.repr u)); temp _u1 (Vlong (Int64.repr (Zlength w1')));
           temp _r (Vint (Int.repr 1));
           temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
           temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
    SEP (data_at Ews (tarray tuchar outlen1) (vb (w1' ++ [0]) ++ R1) po1;
         data_at Ews (tarray tuchar outlen2) (vb (w2' ++ [0]) ++ R2) po2;
         data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) po; TT))
  break: (
    PROP ()
    LOCAL (temp _u2 (Vlong (Int64.repr (Zlength w2'))); temp _u1 (Vlong (Int64.repr (Zlength w1')));
           temp _r (Vint (Int.repr 1));
           temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
           temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
    SEP (data_at Ews (tarray tuchar outlen1) (vb (w1' ++ [0]) ++ R1) po1;
         data_at Ews (tarray tuchar outlen2) (vb (w2' ++ [0]) ++ R2) po2;
         data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb (w1' ++ 46 :: w2' ++ [0]) ++ R) po; TT)).
  { Exists 0. entailer!. }
  { Intros u.
    pose proof (alb26_nz w2' u F2 ltac:(lia)) as Hnz.
    assert (Hb: 0 <= Znth u (w2' ++ [0]) <= 255) by (destruct Hnz; lia).
    forward_if (temp _t'22 (Vint (Int.repr (if zeq u (Zlength w2') then 0 else 1)))).
    { forward.
      { entailer!. rewrite alb26_znth by lia. simpl.
        rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward. entailer!. rewrite alb26_znth by lia.
      destruct Hnz as [[Hu Hz] | [Hlt Hb']].
      { rewrite Hz. destruct (zeq u (Zlength w2')); [ reflexivity | lia ]. }
      rewrite zeq_false by lia. simpl. unfold Int.eq.
      rewrite (Int.unsigned_repr (Znth u (w2' ++ [0]))) by rep_lia.
      destruct (zeq (Znth u (w2' ++ [0])) (Int.unsigned (Int.repr 0))) as [E|E];
        [ rewrite Int.unsigned_repr in E by rep_lia; lia | reflexivity ]. }
    { exfalso; lia. }
    forward_if.
    { destruct (zeq u (Zlength w2')); [ contradiction | ].
      forward. Exists (u + 1). entailer!. }
    { destruct (zeq u (Zlength w2')) as [Hu | ]; [ | discriminate ].
      forward. rewrite Hu. entailer!. } }
  (* gp_assert(r == 1 && bytes_eq(out, out1, u1) && out[u1] == '.' && bytes_eq(out + u1 + 1, out2, u2 + 1)) *)
  unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS. subst Delta POSTCONDITION MORE_COMMANDS.
  apply alb26_check; auto.
Qed.
