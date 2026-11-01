(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma body_maxmaxsize_ok : semax_body Vprog Gprog_none f_maxmaxsize maxmaxsize_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if orb (8 <=? lb) (lb =? 0) then 1 else 0)));
                            temp _lenbytes (Vlong (Int64.repr lb))) SEP ()).
  - forward. entailer!. rewrite (proj2 (Z.leb_le 8 lb)) by lia. reflexivity.
  - forward. entailer!. rewrite (proj2 (Z.leb_gt 8 lb)) by lia. simpl. unfold Int64.eq.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Z.eqb_spec lb 0); destruct (zeq lb 0); try lia; reflexivity.
  - destruct (_ || _)%bool eqn:E; forward_if.
    + forward. entailer!. unfold maxmaxsize_model. rewrite E.
      f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity.
    + inv H0.
    + contradiction.
    + apply orb_false_iff in E. destruct E as [E1 E2]. apply Z.leb_gt in E1. apply Z.eqb_neq in E2. forward.
      * entailer!. rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small lb) by rep_lia.
        rewrite Z.mod_small by rep_lia. lia.
      * entailer!. unfold maxmaxsize_model.
        assert (lb = 1 \/ lb = 2 \/ lb = 3 \/ lb = 4 \/ lb = 5 \/ lb = 6 \/ lb = 7) as HH by lia.
        repeat destruct HH as [HH|HH]; subst; reflexivity.
Qed.
