(* The bodies of the helpers of ossl_punycode_decode: adapt, is_basic, digit_decoded (crypto/punycode.c), under
   Punycode.CS. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.BodyDecAdapt.

Ltac one_zero :=
  match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end.

Lemma body_is_basic_aux : semax_body Vprog Gprog_none f_is_basic is_basic_spec.
Proof.
  start_function.
  forward_if (PROP() LOCAL(temp _t'1 (Vint (Int.repr (if a <? 128 then 1 else 0)))) SEP()).
  - forward. entailer!. destruct (Z.ltb_spec a 128); [auto|lia].
  - forward. entailer!. destruct (Z.ltb_spec a 128); [lia|auto].
  - forward.
Qed.

Lemma body_digit_decoded_aux : semax_body Vprog Gprog_none f_digit_decoded digit_decoded_spec.
Proof.
  start_function.
  forward_if (PROP() LOCAL(temp _t'1 (Vint (Int.repr (if andb (65 <=? a) (a <=? 90) then 1 else 0))); temp _a (Vint (Int.repr a))) SEP()).
  { forward. entailer!. destruct (Z.leb_spec 65 a); [|lia]; destruct (zlt 90 a), (Z.leb_spec a 90); simpl; auto; lia. }
  { forward. entailer!. destruct (Z.leb_spec 65 a); [lia|]; reflexivity. }
  forward_if.
  { forward. entailer!. unfold digit_value.
    destruct (Z.leb_spec 65 a), (Z.leb_spec a 90); simpl in *; try congruence. f_equal; f_equal.
    destruct (Z.eqb_spec (a - 65) 36); lia. }
  forward_if (PROP() LOCAL(temp _t'2 (Vint (Int.repr (if andb (97 <=? a) (a <=? 122) then 1 else 0))); temp _a (Vint (Int.repr a))) SEP()).
  { forward. entailer!. destruct (Z.leb_spec 97 a); [|lia]; destruct (zlt 122 a), (Z.leb_spec a 122); simpl; auto; lia. }
  { forward. entailer!. destruct (Z.leb_spec 97 a); [lia|]; reflexivity. }
  forward_if.
  { forward. entailer!. unfold digit_value.
    destruct (Z.leb_spec 65 a), (Z.leb_spec a 90), (Z.leb_spec 97 a), (Z.leb_spec a 122); simpl in *; try one_zero; try lia.
    f_equal; f_equal. destruct (Z.eqb_spec (a - 97) 36); lia. }
  forward_if (PROP() LOCAL(temp _t'3 (Vint (Int.repr (if andb (48 <=? a) (a <=? 57) then 1 else 0))); temp _a (Vint (Int.repr a))) SEP()).
  { forward. entailer!. destruct (Z.leb_spec 48 a); [|lia]; destruct (zlt 57 a), (Z.leb_spec a 57); simpl; auto; lia. }
  { forward. entailer!. destruct (Z.leb_spec 48 a); [lia|]; reflexivity. }
  forward_if.
  { forward. entailer!. unfold digit_value.
    destruct (Z.leb_spec 65 a), (Z.leb_spec a 90), (Z.leb_spec 97 a), (Z.leb_spec a 122), (Z.leb_spec 48 a), (Z.leb_spec a 57);
      simpl in *; try one_zero; try lia.
    f_equal; f_equal. destruct (Z.eqb_spec (a - 48 + 26) 36); lia. }
  forward. entailer!. unfold digit_value.
  destruct (Z.leb_spec 65 a), (Z.leb_spec a 90), (Z.leb_spec 97 a), (Z.leb_spec a 122), (Z.leb_spec 48 a), (Z.leb_spec a 57);
    simpl in *; try one_zero; try lia; reflexivity.
Qed.

Lemma decode_helper_bodies :
  semax_body Vprog Gprog_none f_adapt adapt_spec /\
  semax_body Vprog Gprog_none f_is_basic is_basic_spec /\
  semax_body Vprog Gprog_none f_digit_decoded digit_decoded_spec.
Proof.
  split; [exact body_adapt_aux | split; [exact body_is_basic_aux | exact body_digit_decoded_aux]].
Qed.
