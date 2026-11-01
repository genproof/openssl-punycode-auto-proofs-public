(* Piece 15 of the main of harness/x_decode.c: gp_assert(same_uints(out, want, cap)), gp_assert(same_bytes(enc, snap,
   len)), return 0 (DecMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecProg.
Require Import OpensslPunycode.proof.harness.decode.DecMainDefs.
Require OpensslPunycode.proof.harness.ARDecRange.

#[local] Instance CCE_rt : change_composite_env OpensslPunycode.proof.harness.RefRt.CS CS := CCE_any _ _.
#[local] Instance CCE_rt' : change_composite_env CS OpensslPunycode.proof.harness.RefRt.CS := CCE_any _ _.

(* The code points ossl_punycode_decode leaves in out (and pr_decode in want). *)
Definition res_list (bs init: list Z) : list Z :=
  if Int.max_unsigned <=? Zlength bs then init else
  let (ok, out) := decode bs (Zlength init) in out ++ sublist (Zlength out) (Zlength init) init.

Lemma res_list_ok (bs init: list Z):
  bytes_ok bs -> Forall (fun x => 0 <= x <= Int.max_unsigned) init ->
  snd (fst (dres bs init)) = vb (res_list bs init) /\
  Forall (fun x => 0 <= x <= Int.max_unsigned) (res_list bs init) /\
  Zlength (res_list bs init) = Zlength init.
Proof.
  intros Hb Hi. unfold dres, res_list, OpensslPunycode.proof.punycode.PunySpec.decode_result.
  destruct (Int.max_unsigned <=? Zlength bs); [ auto | ].
  pose proof (OpensslPunycode.proof.harness.ARDecRange.decode_out_range bs (Zlength init) Hb (Zlength_nonneg _))
    as [Hr Hl].
  destruct (decode bs (Zlength init)) as [ok out]. simpl in *.
  pose proof (Zlength_nonneg out).
  split; [ | split ].
  - unfold vb. rewrite map_app, sublist_map. reflexivity.
  - apply Forall_app; split.
    + eapply Forall_impl; [ | exact Hr ]. intros x Hx. unfold maxint in Hx. rep_lia.
    + apply Forall_sublist; auto.
  - rewrite Zlength_app, Zlength_sublist by lia. lia.
Qed.

Local Open Scope logic.

Lemma piece15 : piece15_stmt.
Proof.
  intros Espec gv vc vo vd bs pe ps init po pw. unfold pre15, T15, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  destruct (res_list_ok bs init H H2) as [E [Hr Hl]].
  rewrite E. set (L := res_list bs init) in *. clearbody L.
  forward.
  rewrite <- Hl.
  rewrite (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength L) _ po).
  rewrite (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength L) _ pw).
  forward_call (Ews, po, L, Ews, pw, L).
  destruct (list_eq_dec Z.eq_dec L L) as [_ | NE]; [ | contradiction NE; reflexivity ].
  forward_call (Int.repr 1).
  rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ pe).
  rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength bs) _ ps).
  forward_call (Ews, pe, bs, Ews, ps, bs).
  destruct (list_eq_dec Z.eq_dec bs bs) as [_ | NE]; [ | contradiction NE; reflexivity ].
  forward_call (Int.repr 1).
  forward. Exists (Int.repr 0). entailer!.
Qed.
