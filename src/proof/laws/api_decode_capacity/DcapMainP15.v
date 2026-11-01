(* Piece 15 of the main of harness/api_decode_capacity.c: when count > 0, fewer = any_uints(count - 1), its NULL
   test, the decode into count - 1 elements, which fails and keeps the length (DcapMainDefs). *)
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

(* A pointer from any_uints may be compared with NULL. *)
Lemma mblock_ui_tc n v q P: 0 <= n -> mblock_ui n v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold mblock_ui. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - sep_apply (data_at_data_at_ Ews (tarray tuint n) v q).
    destruct (zlt 0 (sizeof (tarray tuint n))).
    + sep_apply (data_at__valid_ptr Ews (tarray tuint n) q); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews (tarray tuint n) q); [ lia | ]. entailer!.
Qed.

Lemma data_at_arr0_ui {cs: compspecs} sh n v q: data_at sh (tarray tuint n) v q |-- arr0 sh tuint n v q * TT.
Proof. unfold arr0. destruct (Z.eq_dec n 0). - rewrite emp_sepcon. apply TT_right. - cancel. Qed.

Lemma piece15 : piece15_stmt.
Proof.
  intros Espec gv vc ve vf bs pi out. unfold pre15, lvars3, T15, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros. destruct H0 as [Hlt [Hol [Hor [Hd Hf]]]]. pose proof (Zlength_nonneg out).
  forward.
  forward_if (PROP () LOCAL (lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
    SEP (data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf; TT)).
  - forward.
    forward_call (Zlength out - 1, gv).
    Intros vret. destruct vret as [pf vs]. simpl fst in *. simpl snd in *.
    rewrite !(@malloc_token_change_composite CM.CS CS (CCE_any _ _) Ews (tarray tuint _)) by reflexivity.
    rewrite !(data_at_tuint_cs CM.CS CS).
    fold (mblock_ui (Zlength out - 1) (vb vs) pf).
    forward. forward. forward.
    forward_if (PROP (pf <> nullval) LOCAL (temp _fewer pf; temp _input pi;
        temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
        lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
      SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength out - 1) (vb vs) pf;
           data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc;
           data_at_ Tsh tuint ve; data_at Tsh tuint (Vint (Int.repr (Zlength out - 1))) vf;
           PS.puny_consts gv; mem_mgr gv; TT)).
    + apply derives_trans with (mblock_ui (Zlength out - 1) (vb vs) pf * TT); [ cancel | apply mblock_ui_tc; lia ].
    + forward. Exists (Int.repr 0). entailer!.
    + forward. unfold mblock_ui. rewrite if_false by auto.
      sep_apply (data_at_arr0_ui Ews (Zlength out - 1) (vb vs) pf). entailer!.
    + Intros.
      assert (Hne: out <> []) by (intro E; subst; rewrite Zlength_nil in H1; lia).
      specialize (Hf Hne).
      destruct (decode bs (Zlength out - 1)) as [ok fo] eqn:HD. simpl in Hf. subst ok.
      forward_call (gv, Ews, pi, bs, Ews, pf, Zlength out - 1, vb vs, Tsh, vf).
      { rewrite Zlength_vb; auto. }
      rewrite (DecModel.decode_result_eq bs (Zlength out - 1) (vb vs) false fo Hlt HD). simpl fst; simpl snd.
      forward_call (Int.one).
      forward. forward.
      forward_call (Int.one).
      { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
      entailer!.
  - forward. entailer!.
  - forward. Exists (Int.repr 0). entailer!.
Qed.
