(* The body of pr_a2ulabel (harness/puny_ref.h) under the a2ulabel harness's compspecs, from its pieces. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Require Import OpensslPunycode.proof.harness.ARFind.
Require Import OpensslPunycode.proof.harness.ARTest.
Require Import OpensslPunycode.proof.harness.ARNonAce.
Require Import OpensslPunycode.proof.harness.ARAce1.
Require Import OpensslPunycode.proof.harness.ARCp.
Require Import OpensslPunycode.proof.harness.ARRest.
Require Import OpensslPunycode.proof.harness.ARTail.
Local Open Scope logic.

Lemma body_pr_a2ulabel_main : semax_body Vprog Gprog_a2ulabel f_pr_a2ulabel pr_a2ulabel_spec.
Proof.
start_function.
assert (CTX: ar_ctx shs ps s shk cap init shb shc) by (unfold ar_ctx; tauto).
forward. forward. forward.
unfold MORE_COMMANDS, abbreviate.
eapply semax_seq.
2:{ apply (tail_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u); auto. }
eapply semax_pre.
2:{ apply semax_loop with (Q := ar_inv shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u)
    (Q' := ar_inv shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u).
  2:{ eapply semax_post_flipped; [apply semax_skip| ..]; intros; apply andp_left2; first [apply derives_refl | apply FF_left]. }
  unfold ar_inv at 1. Intros st k cv.
  assert (OK: it_ok s cap st k cv) by (unfold it_ok; auto).
  apply -> semax_skip_seq.
  forward.
  eapply semax_seq.
  { eapply semax_pre; [| apply (find_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto].
    unfold find_pre. entailer!. }
  unfold find_post.
  unfold MORE_COMMANDS, abbreviate.
  forward.
  rewrite sub64_repr.
  eapply semax_seq.
  2:{ apply (rest_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto. }
  eapply semax_pre with (P' := lab_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv).
  { unfold lab_pre. entailer!. }
  eapply semax_seq.
  { apply (test_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto. }
  unfold test_post.
  unfold MORE_COMMANDS, abbreviate.
  forward_if.
  { destruct (is_ace (lab s st)) eqn:ACE; [ | match goal with HF: typed_true _ Vfalse |- _ => inv HF end ].
    unfold MORE_COMMANDS, abbreviate.
    eapply semax_pre;
      [ | apply (ace1_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto ].
    { unfold lab_pre. entailer!. }
    intros cps LEN DEC. apply (cp_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv); auto. }
  { destruct (is_ace (lab s st)) eqn:ACE; [ match goal with HT: typed_false _ Vtrue |- _ => inv HT end | ].
    eapply semax_pre;
      [ | apply (nonace_piece shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv
                  (normal_ret_assert (lab_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k)));
          auto ].
    unfold lab_pre. entailer!. } }
unfold ar_inv. Exists 0 (@nil Z, false) cinit. entailer!.
split; [ split; [ rewrite Zlength_nil; lia | constructor ] | rewrite rem_0; reflexivity ].
Qed.
