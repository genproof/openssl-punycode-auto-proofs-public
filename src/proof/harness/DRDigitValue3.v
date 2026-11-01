(* pr_digit_value (harness/puny_ref.h): the tail of its body from the test 48..57 on (the body is split over
   DRDigitValue3, DRDigitValue2, DRDigitValue to keep each file short). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.

Definition stmt_dv3 : statement := (Ssequence (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _c tuchar) (Econst_int (Int.repr 48) tint) tint) (Sset _t'3 (Ecast (Ebinop Ole (Etempvar _c tuchar) (Econst_int (Int.repr 57) tint) tint) tbool)) (Sset _t'3 (Econst_int (Int.repr 0) tint))) (Sifthenelse (Etempvar _t'3 tint) (Sreturn (Some (Ebinop Oadd (Ebinop Osub (Ecast (Etempvar _c tuchar) tulong) (Econst_int (Int.repr 48) tint) tulong) (Econst_int (Int.repr 26) tint) tulong))) Sskip)) (Sreturn (Some (Econst_long (Int64.repr 36) tulong)))).

(* The ret_assert of the body of pr_digit_value (after start_function). *)
Definition dv_post (c: Z) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong (PROP () RETURN (Vlong (Int64.repr (digit_value c))) SEP ()))
    (stackframe_of f_pr_digit_value).

Ltac dvt := unfold digit_value;
  repeat match goal with |- context [if ?b then _ else _] =>
    let E := fresh "E" in destruct b eqn:E; rewrite ?E in *; simpl in * end;
  try discriminate; rewrite ?andb_true_iff, ?Z.leb_le in *; try lia; auto.

Lemma dv_tail3: forall (Espec: OracleKind) c, 0 <= c <= 255 -> ~ (65 <= c <= 90) -> ~ (97 <= c <= 122) ->
  semax (func_tycontext f_pr_digit_value Vprog Gprog_none nil)
    (PROP () LOCAL (temp _c (Vint (Int.repr c))) SEP ()) stmt_dv3 (dv_post c).
Proof.
intros Espec c H N1 N2. unfold stmt_dv3, dv_post. abbreviate_semax.
forward_if (temp _t'3 (Val.of_bool ((48 <=? c) && (c <=? 57))%bool)).
{ forward. entailer!. rewrite (proj2 (Z.leb_le 48 c)) by lia.
  destruct (zlt 57 c); simpl; [rewrite (proj2 (Z.leb_gt c 57)) | rewrite (proj2 (Z.leb_le c 57))]; auto; lia. }
{ forward. entailer!. rewrite (proj2 (Z.leb_gt 48 c)) by lia. auto. }
forward_if.
{ forward. entailer!. dvt. }
forward. entailer!. dvt.
Qed.
