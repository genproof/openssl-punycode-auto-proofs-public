(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Ltac dead_branch := first [discriminate | contradiction |
  match goal with
  | H: Int.repr _ = Int.zero |- _ => inv H
  | H: Int.repr _ <> Int.zero |- _ => exfalso; apply H; reflexivity
  | H: Int.repr _ = Int.repr _ |- _ => inv H
  | H: Int.repr _ <> Int.repr _ |- _ => exfalso; apply H; reflexivity
  | H: ?a <> ?a |- _ => exfalso; apply H; reflexivity
  end].

Lemma ltu_sub: forall cap n len, 0 <= n <= cap -> cap <= Int64.max_unsigned -> 0 <= len <= Int64.max_unsigned ->
  Int64.ltu (Int64.sub (Int64.repr cap) (Int64.repr n)) (Int64.repr len) = (cap - n <? len).
Proof.
  intros. unfold Int64.ltu, Int64.sub. rewrite (Int64.unsigned_repr cap), (Int64.unsigned_repr n) by rep_lia.
  rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (cap - n) len); destruct (Z.ltb_spec (cap - n) len); auto; lia.
Qed.

Lemma body_reserve_bytes_ok :
  semax_body Vprog Gprog_reserve_bytes f_WPACKET_reserve_bytes WPACKET_reserve_bytes_spec.
Proof.
  start_function.
  unfold sub_rec, zblock, pkt_rep. Intros.
  assert_PROP (isptr sub) as Psub.
  { entailer!. match goal with H: field_compatible _ _ sub |- _ => destruct H; auto end. }
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if len =? 0 then 0 else 1))); temp _pkt pkt;
      temp _len (Vlong (Int64.repr len)); temp _allocbytes pa)
    SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n), (Vlong (Int64.repr cap),
           (sub, Vint Int.zero)))))) pkt;
         data_at shb (tarray tuchar cap) v buf;
         @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub;
         @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) (Zrepeat (Vint Int.zero) sub_size) sub;
         data_at_ sha (tptr tuchar) pa)).
  - forward. entailer!. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Z.eqb_spec len 0); destruct (zeq len 0); try lia; reflexivity.
  - subst sub; contradiction.
  - destruct (len =? 0) eqn:EL.
    + forward_if.
      * forward. simpl orb. unfold sub_rec, zblock, pkt_rep. cancel.
      * dead_branch.
    + apply Z.eqb_neq in EL. forward_if; [dead_branch |].
      forward. forward. forward_if.
      * rewrite ltu_sub in H3 by lia. forward. rewrite H3. simpl orb. unfold sub_rec, zblock, pkt_rep. entailer!.
      * rewrite ltu_sub in H3 by lia.
        forward.
        forward_if (PROP () LOCAL (temp _t'4 (Vint (Int.repr 0)); temp _pkt pkt;
            temp _len (Vlong (Int64.repr len)); temp _allocbytes pa)
          SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n), (Vlong (Int64.repr cap),
                 (sub, Vint Int.zero)))))) pkt;
               data_at shb (tarray tuchar cap) v buf;
               @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub;
               @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) (Zrepeat (Vint Int.zero) sub_size) sub;
               data_at_ sha (tptr tuchar) pa)).
        -- dead_branch.
        -- forward. entailer!.
        -- forward_if (PROP () LOCAL (temp _pkt pkt; temp _len (Vlong (Int64.repr len)); temp _allocbytes pa)
             SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n), (Vlong (Int64.repr cap),
                    (sub, Vint Int.zero)))))) pkt;
                  data_at shb (tarray tuchar cap) v buf;
                  @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub;
                  @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) (Zrepeat (Vint Int.zero) sub_size) sub;
                  data_at_ sha (tptr tuchar) pa)).
           { dead_branch. }
           { forward. entailer!. }
           forward_if (PROP () LOCAL (temp _pkt pkt; temp _len (Vlong (Int64.repr len)); temp _allocbytes pa)
             SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n), (Vlong (Int64.repr cap),
                    (sub, Vint Int.zero)))))) pkt;
                  data_at shb (tarray tuchar cap) v buf;
                  @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub;
                  @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) (Zrepeat (Vint Int.zero) sub_size) sub;
                  data_at sha (tptr tuchar) (offset_val n buf) pa)).
           ++ forward_call (shp, pkt, shb, buf, cap, v, n, Vlong (Int64.repr n), Vlong (Int64.repr cap), sub).
              forward. forward.
              forward_if (PROP () LOCAL (temp _t'6 (Vint (Int.repr 0)); temp _pkt pkt;
                  temp _len (Vlong (Int64.repr len)); temp _allocbytes pa)
                SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n),
                       (Vlong (Int64.repr cap), (sub, Vint Int.zero)))))) pkt;
                     data_at shb (tarray tuchar cap) v buf;
                     @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub;
                     @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size)
                       (Zrepeat (Vint Int.zero) sub_size) sub;
                     data_at sha (tptr tuchar) (offset_val n buf) pa)).
              { dead_branch. }
              { forward. entailer!. }
              forward_if.
              { dead_branch. }
              { forward. entailer!. }
           ++ assert_PROP False by entailer!. contradiction.
           ++ forward. rewrite H3. simpl orb. unfold sub_rec, zblock, pkt_rep. entailer!.
Qed.