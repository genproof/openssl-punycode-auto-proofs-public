(* Piece 5 of the main of harness/rj_decode_invalid.c: literal = last_delimiter(input, len), deltas (where the
   deltas start) and invalid = 0, from pre5 to pre8 (JdiMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiModel.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiMainDefs.
Local Open Scope logic.

Lemma piece5 : piece8_stmt -> piece5_stmt.
Proof.
  intros H8 Espec gv vc bs pi init po. unfold pre5, T5, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi).
  forward_call (Ews, pi, bs).
  rewrite <- (arr0_tuchar_cs CS C.CS _ _ _ pi).
  pose proof (last_delim_range bs) as Hb.
  forward_if (temp _t'7 (Vlong (Int64.repr (jdi_start bs)))).
  { forward. entailer!. unfold jdi_start.
    destruct (last_delim bs =? 0) eqn:E; [ | reflexivity ].
    apply Z.eqb_eq in E. rewrite E in *. rewrite Int64.unsigned_repr in * by rep_lia. lia. }
  { forward. entailer!. unfold jdi_start.
    destruct (last_delim bs =? 0) eqn:E; [ reflexivity | ].
    apply Z.eqb_neq in E. exfalso.
    match goal with H: _ >= _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end. lia. }
  forward. forward.
  eapply semax_pre; [ | apply (H8 Espec gv vc bs pi init po) ].
  unfold pre8. entailer!.
Qed.
