(* A piece of the main of harness/x_roundtrip.c (see MainDefs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.

Lemma a2u_labels_from_no_dot : forall s cur, ~ In 46 s -> labels_from s cur = [cur ++ s].
Proof.
  induction s as [|c s IH]; intros cur Hn; simpl.
  - rewrite app_nil_r; reflexivity.
  - assert (c <> 46) by (intro; apply Hn; left; auto).
    destruct (Z.eqb_spec c 46); [contradiction|].
    rewrite IH by (intro; apply Hn; right; auto).
    rewrite <- app_assoc; reflexivity.
Qed.

Lemma a2u_utf8_nonempty : forall c, c <= 1114111 -> Zlength (utf8 c) =? 0 = false.
Proof.
  intros c Hc; unfold utf8.
  destruct (c <? 128); [reflexivity|].
  destruct (c <? 2048); [reflexivity|].
  destruct (c <? 65536); [reflexivity|].
  destruct (Z.leb_spec c 1114111); [reflexivity|lia].
Qed.

Lemma a2u_put_utf8s : forall cps out cap,
  Forall (fun c => 0 <= c <= 1114111) cps ->
  Zlength out + Zlength (utf8s cps) <= cap ->
  put_utf8s cap (out, false) cps = (true, (out ++ utf8s cps, false)).
Proof.
  induction cps as [|c r IH]; intros out cap HF Hc; simpl.
  - unfold utf8s; simpl; rewrite app_nil_r; reflexivity.
  - inversion HF; subst.
    rewrite a2u_utf8_nonempty by lia.
    unfold utf8s in Hc |- *; simpl in Hc |- *.
    rewrite Zlength_app in Hc.
    pose proof (Zlength_nonneg (concat (map utf8 r))).
    unfold put; simpl.
    rewrite a2u_utf8_nonempty by lia.
    destruct (Z.ltb_spec (cap - Zlength out) (Zlength (utf8 c))); [lia|].
    rewrite IH by (auto; unfold utf8s; rewrite Zlength_app; lia).
    rewrite app_assoc; reflexivity.
Qed.

Lemma a2u_model : decode_encode_stmt -> encode_chars_stmt -> a2u_model_stmt.
Proof.
  intros HDE HEC cps e Hlen HF Henc He Hone.
  assert (Hdec : decode e label_cap = (true, cps)).
  { apply HDE; auto. }
  assert (Hch := HEC cps e ltac:(eapply Forall_impl; [|exact HF]; simpl; rep_lia) Henc).
  assert (Hno : ~ In 46 e).
  { intro Hin. rewrite Forall_forall in Hch. destruct (Hch _ Hin) as [?|[?|[?|[_ Hc]]]]; try lia.
    unfold one_label_ok in Hone. rewrite forallb_forall in Hone. specialize (Hone _ Hc). simpl in Hone. discriminate. }
  unfold a2ulabel, labels.
  rewrite a2u_labels_from_no_dot by (unfold ace; intros [?|[?|[?|[?|?]]]]; try lia; auto).
  simpl a2u_labels.
  unfold label_step.
  assert (Hace : is_ace (ace e) = true) by (unfold is_ace, ace; rewrite Zlength_app; change (Zlength [120;110;45;45]) with 4; simpl; pose proof (Zlength_nonneg e);
    destruct (Z.leb_spec 4 (4 + Zlength e)); [reflexivity|lia]).
  rewrite Hace.
  assert (Hsub : sublist 4 (Zlength (ace e)) (ace e) = e) by (unfold ace; rewrite Zlength_app; change (Zlength [120;110;45;45]) with 4;
    rewrite sublist_app2 by (change (Zlength [120;110;45;45]) with 4; pose proof (Zlength_nonneg e); lia); change (Zlength [120;110;45;45]) with 4; rewrite Z.sub_diag;
    replace (4 + Zlength e - 4) with (Zlength e) by lia; apply sublist_same; lia).
  rewrite Hsub.
  assert (Hm : maxint <=? Zlength e = false) by (apply Z.leb_gt; unfold maxint; lia).
  rewrite Hm, Hdec.
  rewrite (a2u_put_utf8s cps [] (ulen_of cps)) by (auto; unfold ulen_of; rewrite Zlength_nil; lia).
  simpl. unfold put; simpl.
  unfold ulen_of. change (Zlength [0]) with 1; destruct (Z.ltb_spec (Zlength (utf8s cps) + 1 - Zlength (utf8s cps)) 1); [lia|].
  reflexivity.
Qed.
