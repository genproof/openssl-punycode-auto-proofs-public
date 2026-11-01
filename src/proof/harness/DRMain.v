(* The body of pr_decode (harness/puny_ref.h) under the decode harness's compspecs, from its pieces. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Require Import OpensslPunycode.proof.harness.DRDelim.
Require Import OpensslPunycode.proof.harness.DRBasic.
Require Import OpensslPunycode.proof.harness.DRLoop.

Lemma body_pr_decode_main : semax_body Vprog Gprog_decode f_pr_decode pr_decode_spec.
Proof.
start_function.
forward. forward. forward.
change (Int.signed (Int.repr 0)) with 0.
change (Vint (Int.repr 0), Vlong (Int64.repr 0)) with (dec_rep 0 0).
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ apply (delim_block Espec shi pin inp sho pout cap init shd pd); auto. }
pose proof (last_delim_range inp) as LD.
forward_if.
{ try rewrite !Int64.unsigned_repr in H3 by rep_lia.
  forward. entailer!. rewrite decode_fail_cap by lia. simpl.
  rewrite Zlength_nil, sublist_same by lia. unfold dec_rep. cancel. }
try rewrite !Int64.unsigned_repr in H3 by rep_lia.
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ apply (basic_block Espec shi pin inp sho pout cap init shd pd); auto; lia. }
Intros.
forward.
forward_if (temp _pos (Vlong (Int64.repr (if last_delim inp =? 0 then 0 else last_delim inp + 1)))).
{ forward. entailer!.
  match goal with C: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in C by rep_lia end.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. auto. }
{ forward. entailer!.
  match goal with C: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in C by rep_lia end.
  rewrite (proj2 (Z.eqb_eq _ _)) by lia. auto. }
forward. forward. forward.
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
{ eapply semax_pre; [ | apply (loop_block Espec shi pin inp sho pout cap init shd pd); auto; lia ].
  change (Int.signed (Int.repr 0)) with 0. entailer!. }
Intros out.
forward.
match goal with D: decode _ _ = (true, _) |- _ => rewrite D end. simpl.
unfold dec_rep. entailer!.
apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl. normalize. apply andp_left2. apply derives_refl.
Qed.
