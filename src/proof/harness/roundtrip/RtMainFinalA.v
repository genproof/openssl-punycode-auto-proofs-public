(* Model facts for piece_final of the main of harness/x_roundtrip.c (MainFinal.v): the UTF-8 octets, their length,
   the ACE string as a C string. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.

Lemma utf8_ok: forall c, 0 <= c <= 1114111 -> bytes_ok (utf8 c) /\ Zlength (utf8 c) <= 4.
Proof.
  intros c Hc. unfold utf8, bytes_ok.
  destruct (c <? 128) eqn:E1; [ apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1 ].
  { split; [ repeat first [apply Forall_nil | apply Forall_cons]; rep_lia | rewrite !Zlength_cons, Zlength_nil; lia ]. }
  destruct (c <? 2048) eqn:E2; [ apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2 ].
  { split; [ | rewrite !Zlength_cons, Zlength_nil; lia ]. repeat first [apply Forall_nil | apply Forall_cons]; Z.to_euclidean_division_equations; rep_lia. }
  destruct (c <? 65536) eqn:E3; [ apply Z.ltb_lt in E3 | apply Z.ltb_ge in E3 ].
  { split; [ | rewrite !Zlength_cons, Zlength_nil; lia ]. repeat first [apply Forall_nil | apply Forall_cons]; Z.to_euclidean_division_equations; rep_lia. }
  destruct (c <=? 1114111) eqn:E4; [ apply Z.leb_le in E4 | apply Z.leb_gt in E4; lia ].
  split; [ | rewrite !Zlength_cons, Zlength_nil; lia ]. repeat first [apply Forall_nil | apply Forall_cons]; Z.to_euclidean_division_equations; rep_lia.
Qed.

Lemma utf8s_ok: forall cps, Forall (fun c => 0 <= c <= 1114111) cps ->
  bytes_ok (utf8s cps) /\ Zlength (utf8s cps) <= 4 * Zlength cps.
Proof.
  induction cps as [ | c r IH ]; intros H.
  - unfold utf8s, bytes_ok. simpl. split; [ constructor | rewrite Zlength_nil; lia ].
  - inversion H; subst. destruct (IH H3) as [IH1 IH2]. destruct (utf8_ok c H2) as [U1 U2].
    unfold utf8s in *. simpl. unfold bytes_ok in *. rewrite Forall_app, Zlength_app, Zlength_cons.
    split; [ auto | lia ].
Qed.

Lemma str_ok_ace: forall cps e,
  Forall (fun c => 0 <= c <= 1114111) cps -> encode cps = Some e -> one_label_ok cps = true ->
  encode_chars_stmt -> OpensslPunycode.proof.shim.ShimSpec.str_ok (ace e).
Proof.
  intros cps e Hcps He Hone EC.
  assert (Hcps': Forall (fun c => 0 <= c <= Int.max_unsigned) cps).
  { eapply Forall_impl; [ | exact Hcps ]. intros; simpl in *; rep_lia. }
  specialize (EC cps e Hcps' He).
  unfold OpensslPunycode.proof.shim.ShimSpec.str_ok, ace.
  rewrite Forall_app. split; [ repeat first [apply Forall_nil | apply Forall_cons]; rep_lia | ].
  unfold one_label_ok in Hone. rewrite forallb_forall in Hone.
  eapply Forall_impl; [ | exact EC ]. simpl. intros x Hx.
  destruct Hx as [Hx | [Hx | [Hx | [Hx Hin]]]]; try rep_lia.
  specialize (Hone x Hin). rewrite andb_true_iff, !negb_true_iff, !Z.eqb_neq in Hone.
  rewrite Forall_forall in Hcps. specialize (Hcps x Hin). rep_lia.
Qed.
