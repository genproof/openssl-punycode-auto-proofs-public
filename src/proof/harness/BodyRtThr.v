(* The bodies of pr_threshold and pr_digit_char (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

Lemma zext8_repr: forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma body_pr_threshold' : semax_body Vprog Gprog_none f_pr_threshold pr_threshold_spec.
Proof.
  start_function.
  forward_if.
  { forward. unfold threshold. rewrite (proj2 (Z.leb_le k bias)) by lia. entailer!. }
  forward_if.
  { forward. unfold threshold. rewrite (proj2 (Z.leb_gt k bias)) by lia.
    unfold Int64.ltu in H2. rewrite !Int64.unsigned_repr in H2 by rep_lia. if_tac in H2; [discriminate|].
    rewrite (proj2 (Z.leb_le _ _)) by lia. entailer!. }
  forward. unfold threshold. rewrite (proj2 (Z.leb_gt k bias)) by lia.
  unfold Int64.ltu in H2. rewrite !Int64.unsigned_repr in H2 by rep_lia. if_tac in H2; [|discriminate].
  rewrite (proj2 (Z.leb_gt _ _)) by lia. entailer!.
Qed.

Lemma body_pr_digit_char' : semax_body Vprog Gprog_none f_pr_digit_char pr_digit_char_spec.
Proof.
  start_function.
  forward_if (PROP (26 <= d) LOCAL (temp _d (Vlong (Int64.repr d))) SEP ()).
  { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. unfold digit_char.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. entailer!.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite !zext8_repr by lia. auto. }
  { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. entailer!. }
  forward. unfold digit_char. rewrite (proj2 (Z.ltb_ge _ _)) by lia. entailer!.
  rewrite !Int64.Z_mod_modulus_eq, !(Z.mod_small (d - 26)), Z.mod_small by rep_lia.
  rewrite !zext8_repr by lia. auto.
Qed.
