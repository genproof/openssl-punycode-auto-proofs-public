(* The body of pr_utf8, part A: the one- and two-octet cases (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.BodyRtUtf8Lib.
Require Import OpensslPunycode.proof.harness.BodyRtUtf8B.

Lemma body_pr_utf8' : semax_body Vprog Gprog_none f_pr_utf8 pr_utf8_spec.
Proof.
  start_function.
  forward_if (PROP (128 <= c) LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o)
    SEP (arr0 sh tuchar (Zlength (utf8 c)) old o)).
  { rewrite !Int64.unsigned_repr in H1 by rep_lia.
    assert (E: utf8 c = [c]) by (unfold utf8; rewrite (proj2 (Z.ltb_lt _ _)) by lia; auto).
    rewrite E. unfold arr0. rewrite if_false by (rewrite Zlength_cons, Zlength_nil; lia).
    rewrite E in H0. change (Zlength [c]) with 1 in *.
    forward. forward. rewrite E. unfold arr0. rewrite if_false by (rewrite Zlength_cons, Zlength_nil; lia).
    change (Zlength [c]) with 1. entailer!.
    rewrite !zext8_mod, !mod64_mod256, Zmod_mod, (Z.mod_small c) by lia.
    replace (upd_Znth 0 old (Vint (Int.repr c))) with [Vint (Int.repr c)] by list_solve. apply derives_refl. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. lia. }
  forward_if (PROP (2048 <= c) LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o)
    SEP (arr0 sh tuchar (Zlength (utf8 c)) old o)).
  { rewrite !Int64.unsigned_repr in H1 by rep_lia.
    assert (E: utf8 c = [192 + c / 64; 128 + c mod 64])
      by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_lt c 2048)) by lia; auto).
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    rewrite E in H0. change (Zlength [192 + c / 64; 128 + c mod 64]) with 2 in *.
    forward. forward. forward. rewrite upd_2 by auto. utf8_vals.
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    change (Zlength [192 + c / 64; 128 + c mod 64]) with 2. entailer!.
    utf8_fin c. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. lia. }
  (* the rest is utf8_piece_b, proved at func_tycontext, whose function specs (none) are below Delta's *)
  Intros. unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_Delta_subsumption; [ | apply utf8_piece_b; auto].
  unfold Delta, abbreviate.
  split3; [ | | split3; [ | | split]]; intros; simpl; auto.
  match goal with |- match Maps.PTree.get id ?A with Some _ => match Maps.PTree.get id ?B with _ => _ end | None => _ end =>
    let E := fresh in assert (E: A = B) by reflexivity; rewrite E; destruct (Maps.PTree.get id B); auto end.
Qed.
