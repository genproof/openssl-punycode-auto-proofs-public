(* Piece 10 of the main of harness/api_decode_capacity.c: exact = any_uints(count), its NULL test, the decode
   into exactly count elements and its two checks (DcapMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

Require OpensslPunycode.proof.punycode.DecModel.

(* ossl_punycode_decode's specification moves to the law's compspecs (its arrays are scalars). *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.

(* A pointer from malloc may be compared with NULL. *)
Lemma mblock_ui_tc n v q P: 0 <= n -> mblock_ui n v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold mblock_ui. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - sep_apply (data_at_data_at_ Ews (tarray tuint n) v q).
    destruct (zlt 0 (sizeof (tarray tuint n))).
    + sep_apply (data_at__valid_ptr Ews (tarray tuint n) q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews (tarray tuint n) q); [ lia | ]. entailer!.
Qed.

(* A block of n elements is an array of n elements (nothing when n = 0). *)
Lemma data_at_arr0_ui {cs: compspecs} sh n v q: data_at sh (tarray tuint n) v q |-- arr0 sh tuint n v q * TT.
Proof. unfold arr0. destruct (Z.eq_dec n 0). - rewrite emp_sepcon. apply TT_right. - cancel. Qed.

Lemma piece10 : piece15_stmt -> piece10_stmt.
Proof.
  intros H15 Espec gv vc ve vf bs pi out po. unfold pre10, lvars3, T10, ret0, main_post, Delta_main.
  abbreviate_semax. Intros.
  destruct H0 as (Hlb & Hlo & Hr & HD & Hf).
  forward.
  forward_call (Zlength out, gv).
  Intros vret. destruct vret as [pe vs]. simpl fst in *. simpl snd in *.
  rewrite (@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuint _)) by reflexivity.
  rewrite (data_at_tuint_cs CM.CS CS).
  fold (mblock_ui (Zlength out) (vb vs) pe).
  forward. forward. forward.
  forward_if.
  { apply derives_trans with (mblock_ui (Zlength out) (vb vs) pe * TT); [ cancel | apply mblock_ui_tc; rep_lia ]. }
  { forward. Exists (Int.repr 0). entailer!. }
  unfold mblock_ui. rewrite if_false by auto.
  sep_apply (data_at_arr0_ui Ews (Zlength out) (vb vs) pe).
  Intros.
  forward_call (gv, Ews, pi, bs, Ews, pe, Zlength out, vb vs, Tsh, ve).
  { rewrite Zlength_vb; lia. }
  rewrite (DecModel.decode_result_eq bs (Zlength out) (vb vs) true out Hlb HD).
  simpl fst; simpl snd.
  rewrite sublist_nil, app_nil_r.
  forward_call (Int.one).
  forward. forward.
  forward_if (temp _t'13 (Vint Int.one)).
  { forward.
    rewrite (arr0_tuint_cs CS CM.CS Ews (Zlength out) _ pe).
    rewrite (arr0_tuint_cs CS CM.CS Ews (Zlength out) _ po).
    forward_call (Ews, pe, out, Ews, po, out).
    destruct (list_eq_dec Z.eq_dec out out) as [_ | NE]; [ | contradiction NE; reflexivity ].
    rewrite (arr0_tuint_cs CM.CS CS Ews (Zlength out) _ pe).
    rewrite (arr0_tuint_cs CM.CS CS Ews (Zlength out) _ po).
    forward. entailer!. }
  { contradiction. }
  forward_call (Int.one).
  eapply semax_pre; [ | apply (H15 Espec gv vc ve vf bs pi out) ].
  unfold pre15, lvars3. entailer!. unfold dcap_facts; auto.
Qed.
