(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Require Import OpensslPunycode.proof.packet.SubRec.

Lemma body_cleanup_ok : semax_body Vprog Gprog_cleanup f_WPACKET_cleanup WPACKET_cleanup_spec.
Proof.
  start_function.
  unfold wpkt, sub_rec, zblock. Intros.
  assert_PROP (malloc_compatible sub_size sub) as MC.
  { entailer!. }
  sep_apply (zblock_to_sub sub MC).
  assert (NN: sub <> nullval) by (destruct sub; try contradiction; discriminate).
  forward_loop (EX s: val, PROP (s = sub \/ s = nullval) LOCAL (temp _sub s; gvars gv; temp _pkt pkt)
     SEP (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt;
          data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; mem_mgr gv;
          if eq_dec s nullval then shim_state gv fn zf (live - 1)
          else data_at Ews t_sub sub_zero sub * @malloc_token OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) sub *
               shim_state gv fn zf live))
    continue: (PROP () LOCAL (temp _parent nullval; gvars gv; temp _pkt pkt)
     SEP (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt;
          data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; mem_mgr gv;
          shim_state gv fn zf (live - 1)))
    break: (PROP () LOCAL (gvars gv; temp _pkt pkt)
     SEP (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt;
          data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf; mem_mgr gv;
          shim_state gv fn zf (live - 1))).
  - unfold pkt_rep. forward. Exists sub. rewrite if_false by auto. entailer!.
  - Intros s. destruct H4; subst s.
    + rewrite if_false by auto. Intros. forward_if.
      * unfold sub_zero. forward.
        sep_apply (sub_to_bytes sub_zero sub).
        forward_call (gv, sub, sub_size, gv ___stringlit_packet_1, 0, fn, zf, live).
        { rewrite if_false by auto. cancel. }
        rewrite if_false by auto. entailer!.
      * contradiction.
    + rewrite if_true by auto. forward_if.
      * discriminate.
      * forward. entailer!.
  - forward. Exists nullval. rewrite if_true by auto. entailer!.
  - unfold pkt_rep. forward. Exists (nullval, (buf, (Vlong (Int64.repr (Zlength w)), (Vlong (Int64.repr (Zlength w)),
      (Vlong (Int64.repr cap), (nullval, Vint Int.zero)))))). entailer!.
Qed.
