(* Piece 0 of the main of harness/rt_roundtrip.c: m, room, the code points cps, the array out and the block of the
   encoding (TrtMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainDefs.
Local Open Scope logic.

(* A block from malloc or any_uints, split into its token and its contents (jtok, jarr of TrtMainDefs). *)
Lemma trt_split_block {cs: compspecs} t n v q:
  complete_legal_cosu_type t = true ->
  (if eq_dec q nullval then emp else malloc_token Ews (tarray t n) q * data_at Ews (tarray t n) v q)
  |-- jtok t n q * jarr t n v q.
Proof.
  intros Ht. unfold jtok, jarr. destruct (eq_dec q nullval); [ rewrite emp_sepcon; auto | ].
  unfold arr0. destruct (Z.eq_dec n 0); [ subst; entailer! | cancel ].
  apply Zlength_nil_inv in H1. subst. apply data_at_zero_array_inv; auto.
Qed.

Lemma piece0 : piece5_stmt -> piece0_stmt.
Proof.
  intros H5 Espec gv vl vc. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (2305843009213693951). Intros m.
  forward_call (9223372036854775807). Intros room.
  forward_call (m, gv).
  Intros vr. destruct vr as [pc cps]. simpl fst in *; simpl snd in *. subst m.
  forward_call (Zlength cps, gv).
  Intros vr. destruct vr as [po outs]. simpl fst in *; simpl snd in *.
  forward_call (tarray tuchar room, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros pe.
  rewrite data_at__tarray. change (Zrepeat (default_val tuchar) room) with (Zrepeat Vundef room).
  sep_apply (@trt_split_block C.CS tuint (Zlength cps) (vb cps) pc eq_refl). Intros.
  sep_apply (@trt_split_block C.CS tuint (Zlength cps) (vb outs) po eq_refl). Intros.
  sep_apply (@trt_split_block CS tuchar room (Zrepeat Vundef room) pe eq_refl). Intros.
  eapply semax_pre; [ | apply (H5 Espec gv vl vc cps outs room pc po pe) ].
  unfold pre5. entailer!.
Qed.
