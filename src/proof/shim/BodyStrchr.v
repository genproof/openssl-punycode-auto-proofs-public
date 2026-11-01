(* The body of strchr (patch/shim/ossl_shim.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.

Local Open Scope logic.

Lemma body_strchr_: semax_body Vprog Gprog_none f_strchr strchr_spec.
Proof.
  start_function.
  rewrite cstr_tschar by auto.
  assert_PROP (Zlength s + 1 <= Ptrofs.max_unsigned /\ isptr p) as HLp.
  { entailer!. apply fc_len in H1; [tauto | list_solve]. }
  destruct HLp as [HL Hp].
  forward. forward.
  rewrite ?Int.sign_ext_idem by lia. rewrite sign_ext_sbyte by rep_lia.
  pose proof (index_of_range c s).
  forward_loop (EX i: Z, PROP (0 <= i <= Zlength s; i <= index_of c s)
                 LOCAL (temp _i (Vlong (Int64.repr i)); temp _ch (Vint (Int.repr (sbyte c))); temp _s p)
                 SEP (data_at sh (tarray tschar (Zlength s + 1)) (map sv (s ++ [0])) p)).
  - Exists 0. entailer!.
  - Intros i. forward.
    { entailer!. pose proof (str0_Znth s i H ltac:(lia)) as Hz. pose proof (sbyte_range _ Hz).
      rewrite Int.signed_repr by rep_lia. rep_lia. }
    destruct (Z.eq_dec i (Zlength s)).
    + subst i. assert (index_of c s = Zlength s) by lia. rewrite Znth_s0_end.
      forward_if.
      { exfalso. apply sbyte_repr_inj in H5; rep_lia. }
      forward. { rewrite Znth_s0_end. entailer!. } rewrite Znth_s0_end.
      forward_if. { forward. rewrite H4, Z.ltb_irrefl, <- cstr_tschar by auto. entailer!. }
      { exfalso. auto. }
    + rewrite Znth_s0_lt by lia. pose proof (str_ok_Znth s i H ltac:(lia)).
      destruct (index_of_step c s i ltac:(lia) H3) as [Hc Hn].
      forward_if.
      { apply sbyte_repr_inj in H5; try rep_lia. specialize (Hc H5). forward. rewrite Hc.
        replace (i <? Zlength s) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite <- cstr_tschar by auto. entailer!. }
      forward. { rewrite Znth_s0_lt by lia. entailer!. } rewrite Znth_s0_lt by lia. forward_if.
      { exfalso. change (Int.repr 0) with (Int.repr (sbyte 0)) in H6. apply sbyte_repr_inj in H6; rep_lia. }
      forward. Exists (i + 1). entailer!.
      apply Hn. intro E; rewrite E in H5; auto.
Qed.
