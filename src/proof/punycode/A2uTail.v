(* ossl_a2ulabel, label loop: after a label, break at the end of the string, else put '.' and move inptr past it. *)
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
(* The model: no '.' left, the conversion ends with this label. *)
Lemma tail_none: forall cap k rest, index_of 46 rest = Zlength rest -> a2u_cont cap k rest = a2u_cont cap k [].
Proof.
  intros. unfold a2u_cont. rewrite H, Z.ltb_irrefl. reflexivity.
Qed.

Lemma rest_at_next: forall s st, 0 <= st <= Zlength s -> index_of 46 (rest_at s st) < Zlength (rest_at s st) ->
  rest_at s (st + index_of 46 (rest_at s st) + 1) =
  sublist (index_of 46 (rest_at s st) + 1) (Zlength (rest_at s st)) (rest_at s st).
Proof.
  intros. pose proof (index_of_range 46 (rest_at s st)).
  unfold rest_at in *. rewrite Zlength_sublist in * by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* The model: a '.' follows the label, put it and go on with the next label. *)
Lemma tail_some: forall cap s st w sh, 0 <= st <= Zlength s ->
  index_of 46 (rest_at s st) < Zlength (rest_at s st) ->
  a2u_cont cap (w, sh) (rest_at s st) =
  a2u_labels cap (fst (put cap (w, false) [46]),
                  orb sh (negb (OpensslPunycode.proof.packet.PacketSpec.put_ok cap w [46])))
    (labels (rest_at s (st + index_of 46 (rest_at s st) + 1))).
Proof.
  intros. unfold a2u_cont. rewrite (proj2 (Z.ltb_lt _ _) H0).
  rewrite put_split, rest_at_next by auto. reflexivity.
Qed.

(* The input string, cut anywhere. *)
Lemma instr_move: forall shi pin s st st',
  field_compatible (tarray tuchar (Zlength s + 1)) [] pin ->
  0 <= st <= Zlength s + 1 -> 0 <= st' <= Zlength s + 1 -> instr shi pin s st = instr shi pin s st'.
Proof.
  intros. unfold instr.
  assert (HL: Zlength (s ++ [0]) = Zlength s + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite <- !(piece_split shi (s ++ [0]) (Zlength s + 1) pin) by (auto; lia). reflexivity.
Qed.

Lemma instr_valid: forall shi pin s st x, readable_share shi ->
  field_compatible (tarray tuchar (Zlength s + 1)) [] pin ->
  0 <= st <= Zlength s -> 0 <= x <= Zlength s -> instr shi pin s st |-- valid_pointer (offset_val x pin).
Proof.
  intros. rewrite (instr_move shi pin s st x) by (auto; lia). unfold instr.
  apply sepcon_valid_pointer2. unfold piece. apply data_at_valid_ptr.
  - apply readable_nonidentity; auto.
  - simpl. rewrite Z.max_r by lia. lia.
Qed.

Lemma a2u_tail_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed
    st R,
  a2u_ctx shi pin s sho out cap init -> 0 <= st <= Zlength s ->
  semax (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil)
    (a2u_lab gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st)
    s_tail
    (a2u_loopR gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed R).
Proof.
  intros. unfold a2u_lab, s_tail. abbreviate_semax. Intros w sh.
  pose proof H as (Hshi & Hsho & Hstr & Hpin & Hfc & Hcap & Hinit & Hout).
  pose proof (index_of_range 46 (rest_at s st)) as Hj.
  assert (Hr: Zlength (rest_at s st) = Zlength s - st) by (unfold rest_at; rewrite Zlength_sublist; lia).
  unfold tmp_at.
  destruct (index_of 46 (rest_at s st) <? Zlength (rest_at s st)) eqn:EJ.
  - apply Z.ltb_lt in EJ.
    forward_if.
    { apply denote_tc_test_eq_split; [|apply valid_pointer_zero64; reflexivity].
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply instr_valid; auto; lia. }
    { exfalso. destruct pin; try contradiction. simpl in H2. discriminate. }
    forward_call (Tsh, vpkt, sho, out, cap, init, w, sub, 46).
    pose proof (tail_some cap s st w sh H0 EJ) as HM. rewrite HM in H1. clear HM.
    forward_if (PROP ()
      LOCAL (temp _tmpptr (offset_val (st + index_of 46 (rest_at s st)) pin); temp _inptr (offset_val st pin);
             temp _result (Vint (Int.repr (res_of (orb sh (negb (PacketSpec.put_ok cap w [46]))))));
             lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
             lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
      SEP (a2u_frame gv out cap tk zf live; PacketSpec.wpkt Tsh vpkt sho out cap init (fst (put cap (w, false) [46])) sub;
           instr shi pin s st; scratch vbuf vbs vseed)).
    { destruct (PacketSpec.put_ok cap w [46]); [discriminate|]. forward. rewrite orb_true_r. entailer!. }
    { destruct (PacketSpec.put_ok cap w [46]);
        [|match goal with H: Int.repr 0 <> Int.zero |- _ => elim H; reflexivity end].
      forward. rewrite orb_false_r. entailer!. }
    forward.
    unfold a2u_loopR, loop1_ret_assert, overridePost. destruct R; cbv beta iota. cbn [tycontext.RA_normal].
    unfold a2u_inv.
    Exists (st + index_of 46 (rest_at s st) + 1) (fst (put cap (w, false) [46]))
      (orb sh (negb (PacketSpec.put_ok cap w [46]))).
    rewrite (instr_move shi pin s st (st + index_of 46 (rest_at s st) + 1)) by (auto; lia).
    destruct pin; try contradiction.
    entailer!.
  - apply Z.ltb_ge in EJ.
    rewrite (tail_none cap (w, sh) (rest_at s st)) in H1 by lia.
    forward_if.
    { forward.
      unfold a2u_loopR, loop1_ret_assert, overridePost. destruct R; cbv beta iota.
      cbn [tycontext.RA_break tycontext.RA_normal].
      unfold a2u_brk. Exists st w sh (res_of sh).
      entailer!. right. split; auto. }
    { exfalso. apply H2. reflexivity. }
Qed.
