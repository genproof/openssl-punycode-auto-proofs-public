(* The body of pr_digit_value (harness/puny_ref.h) under the decode harness's compspecs: the test 65..90, then
   DRDigitValue2. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRDigitValue3.
Require Import OpensslPunycode.proof.harness.DRDigitValue2.

Lemma body_pr_digit_value_proof : semax_body Vprog Gprog_none f_pr_digit_value pr_digit_value_spec.
Proof.
start_function.
unfold Byte.max_unsigned in H; simpl in H.
forward_if (temp _t'1 (Val.of_bool ((65 <=? c) && (c <=? 90))%bool)).
{ forward. entailer!. rewrite (proj2 (Z.leb_le 65 c)) by lia.
  destruct (zlt 90 c); simpl; [rewrite (proj2 (Z.leb_gt c 90)) | rewrite (proj2 (Z.leb_le c 90))]; auto; lia. }
{ forward. entailer!. rewrite (proj2 (Z.leb_gt 65 c)) by lia. auto. }
forward_if.
{ forward. entailer!. dvt. }
assert (N1: ~ (65 <= c <= 90)).
{ intro. match goal with C: typed_false _ _ |- _ => rewrite (proj2 (Z.leb_le 65 c)), (proj2 (Z.leb_le c 90)) in C by lia;
    inv C end. }
(* Delta_specs is opaque after start_function: subsume the piece's type context. *)
eapply semax_Delta_subsumption; [ | eapply semax_pre; [ | apply (dv_tail2 Espec c); auto ] ].
{ unfold Delta, abbreviate. split3; [ | | split3; [ | | split]]; intros; simpl; auto.
  match goal with |- match Maps.PTree.get id ?A with Some _ => match Maps.PTree.get id ?B with _ => _ end
                     | None => _ end =>
    replace B with A by reflexivity; destruct (Maps.PTree.get id A); auto end. }
entailer!.
Qed.
