(* The body of strlen (patch/shim/ossl_shim.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.

Local Open Scope logic.

Lemma body_strlen_: semax_body Vprog Gprog_none f_strlen strlen_spec.
Proof.
  start_function.
  rewrite cstr_tschar by auto.
  assert_PROP (Zlength s + 1 <= Ptrofs.max_unsigned) as HL.
  { entailer!. destruct H0 as (Hp & _ & Hs & _). destruct p; try contradiction. simpl in Hs.
    rewrite Z.max_r in Hs by (pose proof (Zlength_nonneg s); lia). pose proof (Ptrofs.unsigned_range i). rep_lia. }
  forward.
  forward_loop (EX n: Z, PROP (0 <= n <= Zlength s) LOCAL (temp _n (Vlong (Int64.repr n)); temp _s p)
                 SEP (data_at sh (tarray tschar (Zlength s + 1)) (map sv (s ++ [0])) p))
    break: (PROP () LOCAL (temp _n (Vlong (Int64.repr (Zlength s))); temp _s p)
                 SEP (data_at sh (tarray tschar (Zlength s + 1)) (map sv (s ++ [0])) p)).
  - Exists 0. entailer!.
  - Intros n. forward.
    { entailer!. pose proof (str0_Znth s n H ltac:(lia)) as Hz. pose proof (sbyte_range _ Hz).
      rewrite Int.signed_repr by rep_lia. rep_lia. }
    destruct (Z.eq_dec n (Zlength s)).
    + subst. rewrite Znth_s0_end. forward_if. { discriminate. } forward. entailer!.
    + rewrite Znth_s0_lt by lia. pose proof (str_ok_Znth s n H ltac:(lia)).
      forward_if.
      * forward. Exists (n + 1). entailer!.
      * exfalso. change (Int.repr 0) with (Int.repr (sbyte 0)) in H2. apply sbyte_repr_inj in H2; lia.
  - forward. rewrite <- cstr_tschar by auto. entailer!.
Qed.
