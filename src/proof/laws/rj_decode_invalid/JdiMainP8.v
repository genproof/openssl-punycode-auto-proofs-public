(* Piece 8 of the main of harness/rj_decode_invalid.c: the loop over the octets that sets invalid when an octet is
   flagged (not basic before the last delimiter, or without digit-value in the deltas; JdiModel.jdi_bad), from
   pre8 to pre9 (JdiMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiModel.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiMainDefs.
Local Open Scope logic.

(* The harness's test that an octet is a letter or a digit is the test that it has a digit-value. *)
Lemma jdi_digit_test c:
  ((65 <=? c) && (c <=? 90) || (97 <=? c) && (c <=? 122) || (48 <=? c) && (c <=? 57))%bool =
  negb (digit_value c =? 36).
Proof.
  unfold digit_value.
  destruct (Z.leb_spec 65 c), (Z.leb_spec c 90), (Z.leb_spec 97 c), (Z.leb_spec c 122),
    (Z.leb_spec 48 c), (Z.leb_spec c 57); simpl;
    first [ reflexivity | rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity | exfalso; lia ].
Qed.

(* The harness's test of the octet at k sets invalid on a flagged octet. *)
Lemma jdi_flag_step bs k: 0 <= k < Zlength bs ->
  ((k <? last_delim bs) && (128 <=? Znth k bs) || (jdi_start bs <=? k) && (digit_value (Znth k bs) =? 36))%bool =
  true -> flag_ok bs 1.
Proof.
  intros Hk Ht. right. split; [ reflexivity | ]. exists k. split; [ exact Hk | ]. unfold jdi_bad.
  apply orb_true_iff in Ht. destruct Ht as [Ht | Ht]; apply andb_true_iff in Ht; destruct Ht as [H1 H2].
  - left. apply Z.ltb_lt in H1. apply Z.leb_le in H2. lia.
  - right. apply Z.leb_le in H1. apply Z.eqb_eq in H2. lia.
Qed.

(* Closes a goal on the 0/1 value of the harness's comparisons of an octet or an index, by cases on each comparison. *)
Ltac jdi_bool :=
  unfold bool2val in *;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | H: context [?a <=? ?b] |- _ => revert H
  | H: context [?a <? ?b] |- _ => revert H
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | H: context [?a =? ?b] |- _ => revert H
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; intros; simpl in *; try reflexivity; try discriminate; lia.

(* A temporary set by an assignment, whose value is the one the cut wants: the rest of the state is unchanged, so
   the entailment is reflexivity once the two values agree (much faster than entailer!). *)
Ltac jdi_temp :=
  first
  [ match goal with
    | |- ENTAIL _, PROPx _ (LOCALx (temp ?i ?x :: _) _) |-- PROPx _ (LOCALx (temp ?i ?y :: _) _) =>
        replace x with y; [ apply ENTAIL_refl | jdi_bool ]
    end
  | entailer!; jdi_bool ].

Lemma piece8 : piece9_stmt -> piece8_stmt.
Proof.
  intros H9 Espec gv vc bs pi init po. unfold pre8, T8, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  pose proof (last_delim_range bs) as Hld.
  assert (Hst: 0 <= jdi_start bs <= Zlength bs + 1) by (unfold jdi_start; destruct (last_delim bs =? 0); lia).
  forward.
  forward_loop (EX k v, PROP (0 <= k <= Zlength bs; flag_ok bs v)
    LOCAL (temp _i (Vlong (Int64.repr k)); temp _invalid (Vint (Int.repr v));
         temp _deltas (Vlong (Int64.repr (jdi_start bs)));
         temp _literal (Vlong (Int64.repr (last_delim bs)));
         temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
    SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT))
  break: (EX v, PROP (flag_ok bs v)
    LOCAL (temp _invalid (Vint (Int.repr v));
         temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
    SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
  { Exists 0 0. entailer!. left; reflexivity. }
  { Intros k v.
    forward_if.
    { assert (Ha: arr0 Ews tuchar (Zlength bs) (vb bs) pi = data_at Ews (tarray tuchar (Zlength bs)) (vb bs) pi)
        by (unfold arr0; rewrite if_false by lia; reflexivity).
      rewrite Ha.
      assert (Hc: 0 <= Znth k bs <= Byte.max_unsigned) by (apply Forall_Znth; [ exact H | lia ]).
      assert (Hv: Znth k (vb bs) = Vint (Int.repr (Znth k bs))) by (unfold vb; rewrite Znth_map by lia; reflexivity).
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia; lia. }
      unfold vb at 1. rewrite Znth_map by lia. fold (vb bs).
      forward.
      rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
      clear Hv. remember (Znth k bs) as c eqn:Ec.
      forward_if (temp _t'8 (Vint (Int.repr (Z.b2z ((65 <=? c) && (c <=? 90)))))).
      { forward. jdi_temp. }
      { forward. jdi_temp. }
      forward_if (temp _t'9 (Vint (Int.repr (Z.b2z ((65 <=? c) && (c <=? 90) || (97 <=? c) && (c <=? 122)))))).
      { forward. jdi_temp. }
      { forward_if (temp _t'9 (Vint (Int.repr (Z.b2z ((65 <=? c) && (c <=? 90) || (97 <=? c) && (c <=? 122)))))).
        { forward. forward. jdi_temp. }
        { forward. jdi_temp. }
        }
      forward_if (temp _t'10 (Vint (Int.repr (Z.b2z
        ((65 <=? c) && (c <=? 90) || (97 <=? c) && (c <=? 122) || (48 <=? c) && (c <=? 57)))))).
      { forward. jdi_temp. }
      { forward_if (temp _t'10 (Vint (Int.repr (Z.b2z
          ((65 <=? c) && (c <=? 90) || (97 <=? c) && (c <=? 122) || (48 <=? c) && (c <=? 57)))))).
        { forward. forward. jdi_temp. }
        { forward. jdi_temp. }
        }
      forward. rewrite jdi_digit_test.
      forward_if (temp _t'11 (Vint (Int.repr (Z.b2z ((k <? last_delim bs) && (128 <=? c)))))).
      { forward. jdi_temp. }
      { forward. jdi_temp. }
      forward_if (temp _t'12 (Vint (Int.repr (Z.b2z
        ((k <? last_delim bs) && (128 <=? c) || (jdi_start bs <=? k) && (digit_value c =? 36)))))).
      { forward. jdi_temp. }
      { forward_if (temp _t'12 (Vint (Int.repr (Z.b2z
          ((k <? last_delim bs) && (128 <=? c) || (jdi_start bs <=? k) && (digit_value c =? 36)))))).
        { forward. forward. jdi_temp. }
        { forward. jdi_temp. }
        }
      forward_if (EX v', PROP (flag_ok bs v')
        LOCAL (temp _i (Vlong (Int64.repr k)); temp _invalid (Vint (Int.repr v'));
             temp _deltas (Vlong (Int64.repr (jdi_start bs)));
             temp _literal (Vlong (Int64.repr (last_delim bs)));
             temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
             temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
        SEP (arr0 Ews tuint (Zlength init) (vb init) po; data_at Ews (tarray tuchar (Zlength bs)) (vb bs) pi;
             data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
      { forward. Exists 1. entailer!. try subst c. apply (jdi_flag_step bs k); [ lia | assumption ]. }
      { forward. Exists v. entailer!. }
      Intros v'. forward. Exists (k + 1) v'. entailer!. }
    { forward. Exists v. entailer!. } }
  Intros v. eapply semax_pre; [ | apply (H9 Espec gv vc bs pi init po v) ].
  unfold pre9. entailer!.
Qed.
