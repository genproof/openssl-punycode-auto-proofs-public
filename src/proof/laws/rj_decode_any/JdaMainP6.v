(* Piece 6 of the main of harness/rj_decode_any.c: count = cap, r = ossl_punycode_decode(input, len, out, &count) and
   the three checks (JdaMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rj_decode_any.code.
Require Import OpensslPunycode.proof.laws.rj_decode_any.JdaProg.
Require Import OpensslPunycode.proof.laws.rj_decode_any.JdaModel.
Require Import OpensslPunycode.proof.laws.rj_decode_any.JdaMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

Lemma piece6 : piece6_stmt.
Proof.
  intros Espec gv vc bs pi ps init po. unfold pre6, T6, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward.
  rewrite (arr0_tuint_cs CS PS.CS). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  forward_call (gv, Ews, pi, bs, Ews, po, Zlength init, vb init, Tsh, vc).
  { unfold vb. apply Zlength_map. }
  pose proof (jda_result bs (Zlength init) (vb init) H (Zlength_nonneg _)) as Hres. cbv zeta in Hres.
  destruct (PS.decode_result bs (Zlength init) (vb init)) as [[r a] l]. simpl fst in *; simpl snd in *.
  try rewrite <- (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  destruct Hres as [[-> ->] | [-> Hl]].
  - forward_if (temp _t'9 (Vint Int.one)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_call (Int.one).
    forward_if (temp _t'10 (Vint Int.one)).
    { contradiction || discriminate. }
    { forward. forward. entailer!. }
    forward_call (Int.one).
    rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi), (arr0_tuchar_cs CS C.CS _ _ _ ps).
    forward_call (Ews, pi, bs, Ews, ps, bs).
    destruct (list_eq_dec Z.eq_dec bs bs) as [_ | E]; [ | contradiction E; reflexivity ].
    forward_call (Int.one).
    forward. Exists (Int.repr 0). entailer!.
  - forward_if (temp _t'9 (Vint Int.one)).
    { forward. entailer!. }
    { contradiction || discriminate. }
    forward_call (Int.one).
    forward_if (temp _t'10 (Vint Int.one)).
    { forward. forward. entailer!.
      destruct (zlt (Zlength init) l); [ lia | reflexivity ]. }
    { contradiction || discriminate. }
    forward_call (Int.one).
    rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi), (arr0_tuchar_cs CS C.CS _ _ _ ps).
    forward_call (Ews, pi, bs, Ews, ps, bs).
    destruct (list_eq_dec Z.eq_dec bs bs) as [_ | E]; [ | contradiction E; reflexivity ].
    forward_call (Int.one).
    forward. Exists (Int.repr 0). entailer!.
Qed.
