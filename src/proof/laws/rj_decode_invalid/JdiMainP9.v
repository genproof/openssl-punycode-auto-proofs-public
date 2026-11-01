(* Piece 9 of the main of harness/rj_decode_invalid.c: count = cap, r = ossl_punycode_decode(input, len, out, &count)
   and the check `if (invalid) gp_assert(r == 0 && count == cap)` (JdiMainDefs): when the loop flagged an octet,
   JdiModel.jdi_result gives the result 0 and the length cap. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiModel.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

Lemma piece9 : piece9_stmt.
Proof.
  intros Espec gv vc bs pi init po v. unfold pre9, T9, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward.
  rewrite (arr0_tuint_cs CS PS.CS). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  forward_call (gv, Ews, pi, bs, Ews, po, Zlength init, vb init, Tsh, vc).
  { unfold vb. apply Zlength_map. }
  destruct H3 as [-> | [-> [q [Hq Hbad]]]].
  - forward_if True.
    { contradiction || discriminate. }
    { forward. entailer!. }
    forward. Exists (Int.repr 0). entailer!.
  - pose proof (jdi_result bs (Zlength init) (vb init) q Hq Hbad) as [Hr Hl].
    destruct (PS.decode_result bs (Zlength init) (vb init)) as [[r a] l]. simpl fst in *; simpl snd in *.
    subst r l.
    forward_if True.
    { forward_if (temp _t'14 (Vint Int.one)).
      { forward. forward. entailer!. }
      { contradiction || discriminate. }
      forward_call (Int.one).
      entailer!. }
    { contradiction || discriminate. }
    forward. Exists (Int.repr 0). entailer!.
Qed.
