(* Helpers of ARTest*.v (the ACE-prefix test of pr_a2ulabel): model facts, the split of s_test, the middle point. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

Lemma vb_Znth: forall l i, 0 <= i < Zlength l -> Znth i (vb l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold vb. rewrite Znth_map by lia. reflexivity. Qed.

Lemma byte_eq: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply repr_inj_unsigned in E; rep_lia.
Qed.

Lemma is_ace_lab: forall s st, 0 <= st <= Zlength s -> 4 <= lab_end s st - st ->
  is_ace (lab s st) =
  (((Znth st s =? 120) || (Znth st s =? 88)) && ((Znth (st + 1) s =? 110) || (Znth (st + 1) s =? 78))
  && (Znth (st + 2) s =? 45) && (Znth (st + 3) s =? 45))%bool.
Proof.
  intros s st R L. pose proof (lab_end_range s st R).
  unfold is_ace, lab. rewrite Zlength_sublist by lia.
  rewrite !Znth_sublist by lia. replace (0 + st) with st by lia.
  replace (1 + st) with (st + 1) by lia. replace (2 + st) with (st + 2) by lia.
  replace (3 + st) with (st + 3) by lia.
  destruct (4 <=? lab_end s st - st) eqn:E; [reflexivity|]. apply Z.leb_gt in E. lia.
Qed.

Lemma is_ace_short: forall s st, 0 <= st <= Zlength s -> lab_end s st - st < 4 -> is_ace (lab s st) = false.
Proof.
  intros s st R L. pose proof (lab_end_range s st R).
  unfold is_ace, lab. rewrite Zlength_sublist by lia.
  destruct (4 <=? lab_end s st - st) eqn:E; [apply Z.leb_le in E; lia|reflexivity].
Qed.

Ltac fin :=
  repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ =>
      apply repr_inj_unsigned in H; [|rep_lia|rep_lia]
  | H: Int.repr ?a <> Int.repr ?b |- _ =>
      let E := fresh in assert (E: a <> b) by (intro; subst; congruence); clear H
  end;
  repeat (rewrite byte_eq by rep_lia);
  try unfold bool2val;
  repeat match goal with H: typed_true _ _ |- _ => revert H | H: typed_false _ _ |- _ => revert H end;
  repeat match goal with |- context [zeq ?a ?b] => destruct (zeq a b) end;
  repeat match goal with |- context [(?a =? ?b)] =>
    let E := fresh in destruct (a =? b) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E] end;
  intros;
  first [reflexivity | exfalso; lia | unfold typed_true, typed_false in *; simpl in *; discriminate].

Ltac tcv V :=
  rewrite V by lia; entailer!; try rewrite Int.unsigned_repr by rep_lia;
  change Byte.max_unsigned with 255; lia.

(* The values of t'3, t'4, t'5: the first one, two, three octets of the ACE prefix. *)
Definition ace1 (s: list Z) (st: Z) : bool := ((Znth st s =? 120) || (Znth st s =? 88))%bool.
Definition ace2 (s: list Z) (st: Z) : bool := (ace1 s st && ((Znth (st + 1) s =? 110) || (Znth (st + 1) s =? 78)))%bool.
Definition ace3 (s: list Z) (st: Z) : bool := (ace2 s st && (Znth (st + 2) s =? 45))%bool.

(* The four tests of s_test. *)
Definition s_t3 := match s_test with Ssequence (Ssequence (Ssequence x _) _) _ => x | _ => Sskip end.
Definition s_t4 := match s_test with Ssequence (Ssequence (Ssequence _ x) _) _ => x | _ => Sskip end.
Definition s_t5 := match s_test with Ssequence (Ssequence _ x) _ => x | _ => Sskip end.
Definition s_t6 := match s_test with Ssequence _ x => x | _ => Sskip end.

Lemma s_test_split: s_test = Ssequence (Ssequence (Ssequence s_t3 s_t4) s_t5) s_t6.
Proof. reflexivity. Qed.

Section Mid.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

(* After the test of t'3, t'4 or t'5 (4 <= m: the string is a nonempty array): the temp i is v. *)
Definition test_at (i: ident) (v: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp i v;
         temp _m (Vlong (Int64.repr (lab_end s st - st))); temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       data_at shs (tarray tuchar (Zlength s)) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

End Mid.

Lemma arr0_ne: forall {cs: compspecs} sh n v p, n <> 0 -> arr0 sh tuchar n v p = data_at sh (tarray tuchar n) v p.
Proof. intros. unfold arr0. destruct (Z.eq_dec n 0); [lia|reflexivity]. Qed.

Lemma bytes_Znth: forall s i, bytes_ok s -> 0 <= i < Zlength s -> 0 <= Znth i s <= 255.
Proof. intros. unfold bytes_ok in H. rewrite Forall_Znth in H. apply H; auto. Qed.
