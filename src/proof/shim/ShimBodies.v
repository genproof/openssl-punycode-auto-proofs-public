(* The bodies of the shim unit (patch/shim/ossl_shim.c), under Shim.CS. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.
Require Import OpensslPunycode.proof.shim.BodyStrlen.
Require Import OpensslPunycode.proof.shim.BodyStrchr.
Require Import OpensslPunycode.proof.shim.BodyStrncasecmp.
Require Import OpensslPunycode.proof.shim.BodyAlloc.
Require Import OpensslPunycode.proof.shim.BodyFree.

Local Open Scope logic.

Lemma body_BUF_MEM_grow_: semax_body Vprog Gprog_none f_BUF_MEM_grow BUF_MEM_grow_spec.
Proof. start_function. contradiction. Qed.

Lemma body_shim_tolower_: semax_body Vprog Gprog_none f_shim_tolower shim_tolower_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (if andb (65 <=? c) (c <=? 90) then Int.one else Int.zero)); temp _c (Vint (Int.repr c))) SEP ()).
  - forward. entailer!. replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia). simpl.
    destruct (zlt 90 c); [replace (c <=? 90) with false by (symmetry; apply Z.leb_gt; lia)
                         | replace (c <=? 90) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity.
  - forward. entailer!. destruct (65 <=? c) eqn:E2; [apply Z.leb_le in E2; lia | reflexivity].
  - destruct (Z_lt_dec c 65); [ | destruct (Z_le_dec c 90)].
    + assert (Ht: tolower c = c) by (unfold tolower; replace (65 <=? c) with false by (symmetry; apply Z.leb_gt; lia); auto).
      replace (65 <=? c) with false by (symmetry; apply Z.leb_gt; lia). simpl.
      forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr c))) SEP ()). { exfalso; first [discriminate | auto]. } forward. entailer!.
      forward; rewrite Ht; entailer!.
    + assert (Ht: tolower c = c + 32) by (unfold tolower; replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia);
        replace (c <=? 90) with true by (symmetry; apply Z.leb_le; lia); auto).
      replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia).
      replace (c <=? 90) with true by (symmetry; apply Z.leb_le; lia). simpl.
      forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (c + 32)))) SEP ()).
      forward. rewrite xor32 by lia. entailer!. { exfalso; first [discriminate | auto]. }
      forward; rewrite Ht; entailer!.
    + assert (Ht: tolower c = c) by (unfold tolower; replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia);
        replace (c <=? 90) with false by (symmetry; apply Z.leb_gt; lia); auto).
      replace (65 <=? c) with true by (symmetry; apply Z.leb_le; lia).
      replace (c <=? 90) with false by (symmetry; apply Z.leb_gt; lia). simpl.
      forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr c))) SEP ()). { exfalso; first [discriminate | auto]. } forward. entailer!.
      forward; rewrite Ht; entailer!.
Qed.

Lemma shim_bodies :
  semax_body Vprog Gprog_zalloc f_CRYPTO_zalloc CRYPTO_zalloc_spec /\
  semax_body Vprog Gprog_free f_CRYPTO_free CRYPTO_free_spec /\
  semax_body Vprog Gprog_none f_strlen strlen_spec /\
  semax_body Vprog Gprog_none f_strchr strchr_spec /\
  semax_body Vprog Gprog_none f_shim_tolower shim_tolower_spec /\
  semax_body Vprog Gprog_strncasecmp f_OPENSSL_strncasecmp OPENSSL_strncasecmp_spec /\
  semax_body Vprog Gprog_none f_BUF_MEM_grow BUF_MEM_grow_spec.
Proof.
  split; [exact body_CRYPTO_zalloc_ | ].
  split; [exact body_CRYPTO_free_ | ].
  split; [exact body_strlen_ | ].
  split; [exact body_strchr_ | ].
  split; [exact body_shim_tolower_ | ].
  split; [exact body_OPENSSL_strncasecmp_ | ].
  exact body_BUF_MEM_grow_.
Qed.

Definition body_CRYPTO_zalloc : semax_body Vprog Gprog_zalloc f_CRYPTO_zalloc CRYPTO_zalloc_spec :=
  proj1 shim_bodies.
Definition body_CRYPTO_free : semax_body Vprog Gprog_free f_CRYPTO_free CRYPTO_free_spec :=
  proj1 (proj2 shim_bodies).
Definition body_strlen : semax_body Vprog Gprog_none f_strlen strlen_spec :=
  proj1 (proj2 (proj2 shim_bodies)).
Definition body_strchr : semax_body Vprog Gprog_none f_strchr strchr_spec :=
  proj1 (proj2 (proj2 (proj2 shim_bodies))).
Definition body_shim_tolower : semax_body Vprog Gprog_none f_shim_tolower shim_tolower_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 shim_bodies)))).
Definition body_OPENSSL_strncasecmp :
  semax_body Vprog Gprog_strncasecmp f_OPENSSL_strncasecmp OPENSSL_strncasecmp_spec :=
  proj1 (proj2 (proj2 (proj2 (proj2 (proj2 shim_bodies))))).
Definition body_BUF_MEM_grow : semax_body Vprog Gprog_none f_BUF_MEM_grow BUF_MEM_grow_spec :=
  proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shim_bodies))))).
