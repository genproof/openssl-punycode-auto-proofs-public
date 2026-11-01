(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Require Import OpensslPunycode.proof.packet.PacketBuf.

Ltac dead_branch := first [discriminate | contradiction |
  match goal with
  | H: Int.repr _ = Int.zero |- _ => inv H
  | H: Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: Int.repr _ = Int.repr _ |- _ => inv H
  | H: Int.repr _ <> Int.repr _ |- _ => exfalso; apply H; reflexivity
  end].

Lemma body_put_bytes_ok : semax_body Vprog Gprog_put_bytes f_WPACKET_put_bytes__ WPACKET_put_bytes___spec.
Proof.
  start_function.
  unfold wpkt. Intros. pose proof (Zlength_nonneg w) as LNw.
  destruct (cap - Zlength w <? 1) eqn:E.
  - forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr 1)); lvar _data (tptr tuchar) v_data; temp _pkt pkt;
                               temp _val (Vlong (Int64.repr v)); temp _size (Vlong (Int64.repr 1)))
      SEP (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt; data_at_ Tsh (tptr tuchar) v_data;
           data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; sub_rec sub)).
    + dead_branch.
    + forward_call (shp, pkt, shb, buf, cap, vb w ++ sublist (Zlength w) cap init, Zlength w, sub, 1, Tsh, v_data).
      rewrite E. simpl orb. cbv beta iota. Intros. forward. entailer!.
    + forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr 1)); lvar _data (tptr tuchar) v_data; temp _pkt pkt)
        SEP (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt; data_at_ Tsh (tptr tuchar) v_data;
             data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; sub_rec sub)).
      * forward. entailer!.
      * dead_branch.
      * forward_if; [| dead_branch].
        forward. unfold put_ok, put. simpl fst. simpl snd. rewrite Zlength_cons, Zlength_nil. simpl.
        rewrite E. rewrite (proj2 (Z.leb_gt 1 _)) by (apply Z.ltb_lt in E; lia). simpl.
        unfold wpkt. entailer!.
  - apply Z.ltb_ge in E.
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr 0)); lvar _data (tptr tuchar) v_data; temp _pkt pkt;
                               temp _val (Vlong (Int64.repr v)); temp _size (Vlong (Int64.repr 1)))
      SEP (data_at shp t_pkt (pkt_rep buf (Zlength w + 1) cap sub) pkt;
           data_at Tsh (tptr tuchar) (offset_val (Zlength w) buf) v_data;
           data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; sub_rec sub)).
    + dead_branch.
    + forward_call (shp, pkt, shb, buf, cap, vb w ++ sublist (Zlength w) cap init, Zlength w, sub, 1, Tsh, v_data).
      rewrite (proj2 (Z.ltb_ge _ _) E). simpl orb. cbv beta iota. Intros. forward. entailer!.
    + assert_PROP (field_compatible (tarray tuchar cap) [] buf) as FC by entailer!.
      rewrite (sublist_split (Zlength w) (Zlength w + 1) cap init) by lia.
      rewrite (buf_split3 shb cap buf (vb w) _ _ (Zlength w) (Zlength w + 1)) by
        (first [assumption | rewrite Zlength_vb; lia | rewrite Zlength_sublist by rep_lia; lia | lia]).
      replace (Zlength w + 1 - Zlength w) with 1 by lia.
      rewrite (sublist_len_1 (Zlength w)) by lia.
      rewrite (data_at_singleton_array_eq shb tuchar (Znth (Zlength w) init)) by reflexivity.
      Intros.
      forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr 0)); lvar _data (tptr tuchar) v_data; temp _pkt pkt)
        SEP (data_at shp t_pkt (pkt_rep buf (Zlength w + 1) cap sub) pkt;
             data_at Tsh (tptr tuchar) (offset_val (Zlength w) buf) v_data;
             data_at shb (tarray tuchar (Zlength w)) (vb w) buf;
             data_at shb tuchar (Vint (Int.repr v)) (offset_val (Zlength w) buf);
             data_at shb (tarray tuchar (cap - (Zlength w + 1))) (sublist (Zlength w + 1) cap init)
               (offset_val (Zlength w + 1) buf);
             sub_rec sub)).
      * dead_branch.
      * forward. forward_call (shb, offset_val (Zlength w) buf, Znth (Zlength w) init, v).
        rewrite (proj2 (Z.ltb_lt v 256)) by rep_lia. rewrite (Z.mod_small v 256) by rep_lia.
        forward. entailer!.
      * forward_if; [dead_branch |].
        forward. unfold put_ok, put. simpl fst. simpl snd. rewrite Zlength_cons, Zlength_nil. simpl.
        rewrite (proj2 (Z.ltb_ge _ _) E). rewrite (proj2 (Z.leb_le 1 _)) by lia. simpl.
        unfold wpkt. rewrite Zlength_app, Zlength_cons, Zlength_nil. change (Z.succ 0) with 1.
        rewrite vb_app, <- app_assoc.
        rewrite (buf_split3 shb _ buf (vb w) (vb [v]) _ (Zlength w) (Zlength w + 1)) by
          (first [assumption | rewrite Zlength_vb, Zlength_cons, Zlength_nil; lia | rewrite Zlength_vb; lia |
                  rewrite Zlength_sublist by rep_lia; lia | lia]).
        replace (Zlength w + 1 - Zlength w) with 1 by lia.
        rewrite (data_at_singleton_array_eq shb tuchar (Vint (Int.repr v))) by reflexivity.
        entailer!.
        apply Forall_app; split; auto.
Qed.
