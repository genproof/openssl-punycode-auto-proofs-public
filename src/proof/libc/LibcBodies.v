(* The bodies of the libc functions the laws reach (memcpy, memset), under Libc.CS. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.libc.LibcSpec.
Require Import OpensslPunycode.libc.code.

Lemma body_memcpy_proof : semax_body Vprog [] f_memcpy memcpy_spec.
Proof.
  start_function.
  unfold arr0.
  forward. forward.
  destruct (Z.eq_dec (Zlength l) 0) as [E|E].
  - forward_for_simple_bound (Zlength l)
      (EX i: Z, PROP () LOCAL (temp _d d; temp _s s; temp _dest d; temp _n (Vlong (Int64.repr (Zlength l))))
       SEP (emp; emp)).
    + entailer!.
    + lia.
    + forward. unfold arr0. destruct (Z.eq_dec (Zlength l) 0); [|lia]. entailer!.
  - forward_for_simple_bound (Zlength l)
      (EX i: Z, PROP () LOCAL (temp _d d; temp _s s; temp _dest d; temp _n (Vlong (Int64.repr (Zlength l))))
       SEP (data_at shd (tarray tuchar (Zlength l)) (vb (sublist 0 i l) ++ sublist i (Zlength l) dold) d;
            data_at shs (tarray tuchar (Zlength l)) (vb l) s)).
    + entailer!. rewrite sublist_nil, sublist_same by lia. simpl. cancel.
    + assert (Hb: 0 <= Znth i l <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth l _) H); lia).
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward.
      entailer!. unfold vb. rewrite Znth_map by lia. simpl. apply derives_refl'. f_equal. list_solve.
    + forward. unfold arr0. destruct (Z.eq_dec (Zlength l) 0); [lia|].
      entailer!. rewrite sublist_same, sublist_nil, app_nil_r by lia. cancel.
Qed.

Lemma zero_ext_8_repr: forall c, Int.zero_ext 8 (Int.repr c) = Int.repr (c mod 256).
Proof.
  intros. apply Int.same_if_eq. unfold Int.eq.
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite (Int.unsigned_repr (c mod 256)) by (pose proof (Z.mod_pos_bound c 256); rep_lia).
  rewrite Int.unsigned_repr_eq.
  change (2 ^ 8) with 256. change Int.modulus with (256 * 16777216).
  rewrite Z.rem_mul_r, Z.mul_comm, Z_mod_plus_full by lia.
  change (two_p 8) with 256. rewrite Z.mod_mod by lia. apply zeq_true.
Qed.

Lemma body_memset_proof : semax_body Vprog [] f_memset memset_spec.
Proof.
  start_function.
  unfold arr0.
  forward.
  destruct (Z.eq_dec n 0) as [E|E].
  - forward_for_simple_bound n
      (EX i: Z, PROP () LOCAL (temp _p p; temp _s p; temp _c (Vint (Int.repr c)); temp _n (Vlong (Int64.repr n)))
       SEP (emp)).
    + entailer!.
    + lia.
    + forward. unfold arr0.
      match goal with |- context [Z.eq_dec ?x 0] => destruct (Z.eq_dec x 0); [|lia] end. entailer!.
  - forward_for_simple_bound n
      (EX i: Z, PROP () LOCAL (temp _p p; temp _s p; temp _c (Vint (Int.repr c)); temp _n (Vlong (Int64.repr n)))
       SEP (data_at sh (tarray tuchar n) (Zrepeat (Vint (Int.repr (c mod 256))) i ++ sublist i n old) p)).
    + entailer!. rewrite sublist_same by lia. simpl. cancel.
    + forward.
      entailer!. rewrite !zero_ext_8_repr, Zmod_mod. apply derives_refl'. f_equal. list_solve.
    + forward. unfold arr0.
      match goal with |- context [Z.eq_dec ?x 0] => destruct (Z.eq_dec x 0); [lia|] end.
      entailer!. rewrite sublist_nil, app_nil_r. cancel.
Qed.

Lemma libc_bodies :
  semax_body Vprog [] f_memcpy memcpy_spec /\
  semax_body Vprog [] f_memset memset_spec.
Proof. split; [apply body_memcpy_proof | apply body_memset_proof]. Qed.

Definition body_memcpy : semax_body Vprog [] f_memcpy memcpy_spec := proj1 libc_bodies.
Definition body_memset : semax_body Vprog [] f_memset memset_spec := proj2 libc_bodies.
