(* pr_digit_value: the tail of its body from the test 97..122 on. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRDigitValue3.

Definition stmt_dv2 : statement := (Ssequence (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _c tuchar) (Econst_int (Int.repr 97) tint) tint) (Sset _t'2 (Ecast (Ebinop Ole (Etempvar _c tuchar) (Econst_int (Int.repr 122) tint) tint) tbool)) (Sset _t'2 (Econst_int (Int.repr 0) tint))) (Sifthenelse (Etempvar _t'2 tint) (Sreturn (Some (Ebinop Osub (Ecast (Etempvar _c tuchar) tulong) (Econst_int (Int.repr 97) tint) tulong))) Sskip)) stmt_dv3).

Lemma dv_tail2: forall (Espec: OracleKind) c, 0 <= c <= 255 -> ~ (65 <= c <= 90) ->
  semax (func_tycontext f_pr_digit_value Vprog Gprog_none nil)
    (PROP () LOCAL (temp _c (Vint (Int.repr c))) SEP ()) stmt_dv2 (dv_post c).
Proof.
intros Espec c H N1. unfold stmt_dv2, dv_post. abbreviate_semax.
forward_if (temp _t'2 (Val.of_bool ((97 <=? c) && (c <=? 122))%bool)).
{ forward. entailer!. rewrite (proj2 (Z.leb_le 97 c)) by lia.
  destruct (zlt 122 c); simpl; [rewrite (proj2 (Z.leb_gt c 122)) | rewrite (proj2 (Z.leb_le c 122))]; auto; lia. }
{ forward. entailer!. rewrite (proj2 (Z.leb_gt 97 c)) by lia. auto. }
forward_if.
{ forward. entailer!. dvt. }
assert (N2: ~ (97 <= c <= 122)).
{ intro. match goal with C: typed_false _ _ |- _ => rewrite (proj2 (Z.leb_le 97 c)), (proj2 (Z.leb_le c 122)) in C by lia;
    inv C end. }
eapply semax_pre; [ | apply dv_tail3; auto ]. entailer!.
Qed.
