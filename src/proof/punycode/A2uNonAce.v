(* ossl_a2ulabel, label loop: a label that is not an A-label is copied (WPACKET_memcpy(&pkt, inptr, delta)). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uModel.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
(* The model: a label that is not an A-label is copied. *)
Lemma nonace_model: forall cap s st w sh,
  a2u_labels cap ([], false) (labels s) = a2u_labels cap (w, sh) (labels (rest_at s st)) ->
  is_ace (label_of (rest_at s st)) = false ->
  a2u_labels cap ([], false) (labels s) =
  a2u_cont cap (fst (put cap (w, false) (label_of (rest_at s st))),
                orb sh (negb (OpensslPunycode.proof.packet.PacketSpec.put_ok cap w (label_of (rest_at s st))))) (rest_at s st).
Proof.
  intros. rewrite H, a2u_labels_first. unfold label_step. rewrite H0. cbv beta iota.
  rewrite put_split. reflexivity.
Qed.

(* The label at st as the source array of WPACKET_memcpy. *)
Lemma label_sublist: forall s st, 0 <= st <= Zlength s ->
  sublist st (st + index_of 46 (rest_at s st)) (s ++ [0]) = label_of (rest_at s st).
Proof.
  intros. pose proof (index_of_range 46 (rest_at s st)).
  unfold rest_at in *. rewrite Zlength_sublist in H0 by lia.
  unfold label_of. rewrite sublist_app1 by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma piece_label: forall {cs: compspecs} shi s pin st, isptr pin -> 0 <= st <= Zlength s ->
  piece shi (s ++ [0]) st (st + Zlength (label_of (rest_at s st))) pin =
  @arr0 cs shi tuchar (Zlength (label_of (rest_at s st))) (vb (label_of (rest_at s st))) (offset_val st pin).
Proof.
  intros. unfold piece. rewrite Zlength_label_of, label_sublist by auto.
  replace (st + index_of 46 (rest_at s st) - st) with (index_of 46 (rest_at s st)) by lia.
  rewrite (data_at_tuchar_cs CS cs). apply data_at_arr0; auto.
  intros E. rewrite <- Zlength_label_of in E. apply Zlength_nil_inv in E. rewrite E. reflexivity.
Qed.

Lemma bytes_ok_label: forall s st, str_ok s -> bytes_ok (label_of (rest_at s st)).
Proof.
  intros. unfold label_of, rest_at, bytes_ok. apply Forall_sublist. apply Forall_sublist.
  eapply Forall_impl; [|exact H]. simpl; intros; lia.
Qed.

Lemma a2u_nonace_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed
    st w sh c9 R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  a2u_labels cap ([], false) (labels s) = a2u_labels cap (w, sh) (labels (rest_at s st)) ->
  is_ace (label_of (rest_at s st)) = false ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (a2u_head gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w sh c9)
    s_nonace
    (overridePost (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st) R).
Proof.
  intros. unfold a2u_head, a2u_lab, instr, s_nonace. abbreviate_semax.
  destruct H as (Hshi & Hsho & Hstr & Hpin & Hfc & Hcap & Hinit & Hout).
  pose proof (nonace_model cap s st w sh H1 H2) as HM.
  pose proof (index_of_range 46 (rest_at s st)) as Hj.
  assert (Hr: Zlength (rest_at s st) = Zlength s - st) by (unfold rest_at; rewrite Zlength_sublist; lia).
  pose proof (Zlength_label_of (rest_at s st)) as HL.
  pose proof (bytes_ok_label s st Hstr) as HB.
  assert (Hs: Zlength s + 1 <= Ptrofs.max_unsigned).
  { destruct pin; try contradiction. destruct Hfc as [_ [_ [SZ _]]]. unfold size_compatible in SZ. simpl sizeof in SZ.
    pose proof (Ptrofs.unsigned_range i). rep_lia. }
  set (l := label_of (rest_at s st)) in *.
  assert (FC: field_compatible (tarray tuchar (Zlength s + 1)) [] pin) by auto.
  rewrite <- HL.
  rewrite (piece_split shi (s ++ [0]) (Zlength s + 1) pin st (st + Zlength l) (Zlength s + 1))
    by (auto; try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (PL: forall cs: compspecs, @arr0 cs shi tuchar (Zlength l) (vb l) (offset_val st pin) =
                                     piece shi (s ++ [0]) st (st + Zlength l) pin)
    by (intros; symmetry; apply piece_label; auto).
  rewrite <- (PL PkCS). Intros.
  forward_call (Tsh, vpkt, sho, out, cap, init, w, sub, shi, offset_val st pin, l).
  rewrite PL.
  destruct (PacketSpec.put_ok cap w l) eqn:EP; [rewrite orb_false_r in HM | rewrite orb_true_r in HM];
  forward_if.
  1,4: (exfalso; first [discriminate | apply H; reflexivity]).
  all: forward.
  all: destruct R; cbv beta iota; cbn [tycontext.RA_normal].
  all: rewrite (piece_split shi (s ++ [0]) (Zlength s + 1) pin st (st + Zlength l) (Zlength s + 1))
      by (auto; try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  - Exists (fst (put cap (w, false) l)) sh. entailer!.
  - Exists (fst (put cap (w, false) l)) true. entailer!.
Qed.
