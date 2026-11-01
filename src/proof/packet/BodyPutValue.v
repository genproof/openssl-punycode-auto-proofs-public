(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma zero_ext_8_small: forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma low_byte: forall v, 0 <= v <= Int64.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus v) 255)))) =
  Int.repr (v mod 256).
Proof.
  intros. rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small v) by rep_lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  rewrite (Z.mod_small (v mod 256)) by rep_lia. rewrite !zero_ext_8_small by lia. reflexivity.
Qed.

Lemma body_put_value_ok : semax_body Vprog Gprog_none f_put_value put_value_spec.
Proof.
  start_function.
  forward_if. forward. forward.
  forward_loop (EX k: Z, PROP (k = 0 \/ k = 1)
     LOCAL (temp _data (offset_val (-k) data); temp _value (Vlong (Int64.repr (value / 256 ^ k)));
            temp _len (Vlong (Int64.repr (1 - k))))
     SEP (data_at sh tuchar (if Z.eq_dec k 0 then old else Vint (Int.repr (value mod 256))) data))
    continue: (PROP () LOCAL (temp _data (offset_val (-1) data); temp _value (Vlong (Int64.repr (value / 256)));
            temp _len (Vlong (Int64.repr 1)))
     SEP (data_at sh tuchar (Vint (Int.repr (value mod 256))) data))
    break: (PROP () LOCAL (temp _value (Vlong (Int64.repr (value / 256))))
     SEP (data_at sh tuchar (Vint (Int.repr (value mod 256))) data)).
  - Exists 0. entailer!. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - Intros k. assert_PROP (isptr data) by entailer!. forward_if.
    + destruct H1; subst k; [|discriminate]. change (-0) with 0. change (1-0) with 1.
      rewrite Z.pow_0_r, Z.div_1_r, isptr_offset_val_zero by auto.
      forward. forward. forward. entailer!.
      * split. destruct data; try contradiction. unfold sem_sub_pi; simpl. f_equal. rewrite Ptrofs.sub_add_opp. f_equal.
        rewrite Int64.shru_div_two_p, !Int64.unsigned_repr by rep_lia. reflexivity.
      * rewrite low_byte by lia. auto.
    + forward. destruct H1; subst k.
      * rewrite !Int64.unsigned_repr in H3 by rep_lia. lia.
      * entailer!.
  - forward. Exists 1. entailer!.
  - assert (0 <= value / 256 <= Int64.max_unsigned) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    forward_if.
    + change (let (q, _) := Z.div_eucl value 256 in q) with (value / 256) in H2.
      rewrite !Int64.unsigned_repr in H2 by rep_lia.
      forward. rewrite (proj2 (Z.ltb_ge value 256)). entailer!.
      assert (~ value < 256); [intro; rewrite Z.div_small in H2 by lia; lia | lia].
    + change (let (q, _) := Z.div_eucl value 256 in q) with (value / 256) in H2.
      rewrite !Int64.unsigned_repr in H2 by rep_lia.
      forward. rewrite (proj2 (Z.ltb_lt value 256)). entailer!.
      assert (~ 256 <= value); [intro; assert (1 <= value / 256) by (apply Z.div_le_lower_bound; lia); lia | lia].
Qed.
