(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Require Import OpensslPunycode.proof.packet.PacketBuf.
Require Import QuickProof.Assembly.

Ltac dead_branch := first [discriminate | contradiction |
  match goal with
  | H: Int.repr _ = Int.zero |- _ => inv H
  | H: Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: Int.repr _ = Int.repr _ |- _ => inv H
  | H: Int.repr _ <> Int.repr _ |- _ => exfalso; apply H; reflexivity
  end].

Lemma body_memcpy_ok : semax_body Vprog Gprog_memcpy f_WPACKET_memcpy WPACKET_memcpy_spec.
Proof.
  start_function.
  pose proof (Zlength_nonneg l) as LNl. pose proof (Zlength_nonneg w) as LNw.
  forward_if.
  - forward.
    assert (L0: Zlength l = 0).
    { match goal with HZ: Int64.repr (Zlength l) = Int64.zero |- _ =>
        change Int64.zero with (Int64.repr 0) in HZ; apply repr_inj_unsigned64 in HZ; rep_lia end. }
    unfold put_ok, put. rewrite L0. simpl. entailer!.
  - assert (L0: Zlength l <> 0).
    { intro X. match goal with HZ: Int64.repr (Zlength l) <> _ |- _ => rewrite X in HZ; contradiction end. }
    unfold wpkt. Intros.
    forward_call (shp, pkt, shb, buf, cap, vb w ++ sublist (Zlength w) cap init, Zlength w, sub, Zlength l, Tsh, v_dest).
    rewrite (proj2 (Z.eqb_neq _ _) L0). simpl orb.
    destruct (cap - Zlength w <? Zlength l) eqn:E.
    + forward_if; [| dead_branch].
      forward. unfold put_ok, put. simpl fst. simpl snd. rewrite (proj2 (Z.eqb_neq _ _) L0), E.
      rewrite (proj2 (Z.leb_gt (Zlength l) _)) by (apply Z.ltb_lt in E; lia). simpl. unfold wpkt. entailer!.
    + apply Z.ltb_ge in E. Intros.
      forward_if; [dead_branch |].
      assert_PROP (field_compatible (tarray tuchar cap) [] buf) as FC by entailer!.
      rewrite (sublist_split (Zlength w) (Zlength w + Zlength l) cap init) by lia.
      rewrite (buf_split3 shb cap buf (vb w) _ _ (Zlength w) (Zlength w + Zlength l)) by
        (first [assumption | rewrite Zlength_vb; lia | rewrite Zlength_sublist by rep_lia; lia | lia]).
      replace (Zlength w + Zlength l - Zlength w) with (Zlength l) by lia.
      Intros. forward.
      forward_if (PROP () LOCAL (lvar _dest (tptr tuchar) v_dest; temp _pkt pkt; temp _src src;
                                 temp _len (Vlong (Int64.repr (Zlength l))))
        SEP (data_at shp t_pkt (pkt_rep buf (Zlength w + Zlength l) cap sub) pkt;
             data_at Tsh (tptr tuchar) (offset_val (Zlength w) buf) v_dest;
             data_at shb (tarray tuchar (Zlength w)) (vb w) buf;
             data_at shb (tarray tuchar (Zlength l)) (vb l) (offset_val (Zlength w) buf);
             data_at shb (tarray tuchar (cap - (Zlength w + Zlength l))) (sublist (Zlength w + Zlength l) cap init)
               (offset_val (Zlength w + Zlength l) buf);
             sub_rec sub; arr0 shs tuchar (Zlength l) (vb l) src)).
      * forward.
        forward_call (shb, offset_val (Zlength w) buf, sublist (Zlength w) (Zlength w + Zlength l) init,
                      shs, src, l).
        { unfold arr0. rewrite !if_false by auto.
          rewrite !(data_at_tuchar_cs OpensslPunycode.proof.libc.LibcSpec.CS CS). cancel. }
        { rewrite Zlength_sublist by rep_lia; lia. }
        unfold arr0. rewrite !if_false by auto.
        rewrite !(data_at_tuchar_cs OpensslPunycode.proof.libc.LibcSpec.CS CS).
        entailer!.
      * exfalso. destruct FC as [Hp _]. destruct buf; try contradiction. discriminate.
      * forward.
        unfold put_ok, put. simpl fst. simpl snd. rewrite (proj2 (Z.eqb_neq _ _) L0), (proj2 (Z.ltb_ge _ _) E).
        rewrite (proj2 (Z.leb_le (Zlength l) _)) by lia. simpl.
        unfold wpkt. rewrite Zlength_app.
        rewrite vb_app, <- app_assoc.
        rewrite (buf_split3 shb _ buf (vb w) (vb l) _ (Zlength w) (Zlength w + Zlength l)) by
          (first [assumption | rewrite Zlength_vb; lia | rewrite Zlength_sublist by rep_lia; lia | lia]).
        replace (Zlength w + Zlength l - Zlength w) with (Zlength l) by lia.
        entailer!.
        apply Forall_app; auto.
Qed.