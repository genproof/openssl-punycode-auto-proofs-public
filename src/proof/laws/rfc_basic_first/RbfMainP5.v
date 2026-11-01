(* Piece 5 of the main of harness/rfc_basic_first.c: literal = last_delimiter(input, len), count = cap and
   r = ossl_punycode_decode(input, len, out, &count) (RbfMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfModel.
Require Import OpensslPunycode.harness.rfc_basic_first.code.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* The result of the specification satisfies what the checks need (RbfModel). *)
Lemma rbf_res_of bs cap init:
  rbf_res bs cap (fst (fst (PS.decode_result bs cap init))) (snd (fst (PS.decode_result bs cap init)))
    (snd (PS.decode_result bs cap init)).
Proof.
  unfold PS.decode_result.
  destruct (Int.max_unsigned <=? Zlength bs).
  { split; [ left; reflexivity | split; [ reflexivity | intros; discriminate ] ]. }
  destruct (decode bs cap) as [ok out] eqn:D. simpl fst; simpl snd.
  split; [ destruct ok; auto | split ].
  - intros i Hi Hn. pose proof (rbf_literal_fail bs cap i Hi Hn) as F. rewrite D in F. simpl in F. subst ok.
    reflexivity.
  - intros H. destruct ok; [ | discriminate ]. exists out, (sublist (Zlength out) cap init). auto.
Qed.

Lemma piece5 : piece8_stmt -> piece5_stmt.
Proof.
  intros H8 Espec gv vc bs pi init po. unfold pre5, T5, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi).
  forward_call (Ews, pi, bs).
  rewrite <- (arr0_tuchar_cs CS C.CS _ _ _ pi).
  forward.
  rewrite (arr0_tuint_cs CS PS.CS). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  forward_call (gv, Ews, pi, bs, Ews, po, Zlength init, vb init, Tsh, vc).
  { unfold vb. apply Zlength_map. }
  pose proof (rbf_res_of bs (Zlength init) (vb init)) as Hres.
  destruct (PS.decode_result bs (Zlength init) (vb init)) as [[r a] l]. simpl fst in *; simpl snd in *.
  try rewrite <- (arr0_tuchar_cs CS PS.CS _ _ _ pi).
  try rewrite <- (arr0_tuint_cs CS PS.CS).
  eapply semax_pre; [ | apply (H8 Espec gv vc bs pi (Zlength init) po r a l) ].
  unfold pre8. entailer!.
Qed.
