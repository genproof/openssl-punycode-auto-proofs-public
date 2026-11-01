(* The body of OPENSSL_strncasecmp (patch/shim/ossl_shim.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.

Local Open Scope logic.

Lemma body_OPENSSL_strncasecmp_: semax_body Vprog Gprog_strncasecmp f_OPENSSL_strncasecmp OPENSSL_strncasecmp_spec.
Proof.
  start_function.
  rewrite (cstr_tschar sh1 s1) by auto. rewrite (cstr_tschar sh2 s2) by auto.
  assert_PROP (Zlength s1 + 1 <= Ptrofs.max_unsigned /\ isptr p1 /\ Zlength s2 + 1 <= Ptrofs.max_unsigned /\ isptr p2) as HLp.
  { entailer!. match goal with F1: field_compatible (Tarray tschar (Zlength s1 + 1) noattr) [] p1,
                               F2: field_compatible (Tarray tschar (Zlength s2 + 1) noattr) [] p2 |- _ =>
      apply fc_len in F1; [apply fc_len in F2; [tauto | list_solve] | list_solve] end. }
  destruct HLp as (HL1 & Hp1 & HL2 & Hp2).
  set (L1 := s1 ++ [0]). set (L2 := s2 ++ [0]).
  assert (ZL1: Zlength L1 = Zlength s1 + 1) by (unfold L1; list_solve).
  assert (ZL2: Zlength L2 = Zlength s2 + 1) by (unfold L2; list_solve).
  forward_loop (EX i: Z, PROP (0 <= i <= n; i <= Zlength s1; i <= Zlength s2;
       ncasecmp L1 L2 (Z.to_nat n) = ncasecmp (sublist i (Zlength L1) L1) (sublist i (Zlength L2) L2) (Z.to_nat (n - i)))
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _s1 p1; temp _s2 p2; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh1 (tarray tschar (Zlength s1 + 1)) (map sv L1) p1;
          data_at sh2 (tarray tschar (Zlength s2 + 1)) (map sv L2) p2))
    break: (PROP (ncasecmp L1 L2 (Z.to_nat n) = 0) LOCAL ()
     SEP (data_at sh1 (tarray tschar (Zlength s1 + 1)) (map sv L1) p1;
          data_at sh2 (tarray tschar (Zlength s2 + 1)) (map sv L2) p2)).
  - forward. Exists 0. entailer!. rewrite !sublist_same by lia. rewrite ?Z.sub_0_r. auto.
  - Intros i. match goal with Hq: ncasecmp L1 L2 _ = _ |- _ => rename Hq into Heq end.
    forward_if.
    2: { forward. entailer!. assert (i = n) by lia. subst i. rewrite Z.sub_diag in Heq. rewrite Heq.
      destruct (sublist n (Zlength L1) L1); destruct (sublist n (Zlength L2) L2); reflexivity. }
    pose proof (str0_Znth s1 i H ltac:(lia)) as Hz1. pose proof (str0_Znth s2 i H0 ltac:(lia)) as Hz2.
    fold L1 in Hz1. fold L2 in Hz2.
    pose proof (sbyte_range _ Hz1) as Hb1. pose proof (sbyte_range _ Hz2) as Hb2.
    forward.
    unfold sv at 1.
    forward_call (sbyte (Znth i L1)).
    forward.
    unfold sv at 1.
    forward_call (sbyte (Znth i L2)).
    pose proof (tolower_range _ Hb1). pose proof (tolower_range _ Hb2).
    forward. rewrite sub_repr.
    assert (Hk: Z.to_nat (n - i) = S (Z.to_nat (n - (i + 1)))) by lia.
    rewrite Hk, ncasecmp_step in Heq by lia. cbv zeta in Heq.
    forward_if.
    { forward. fold L1 L2. rewrite Heq. destruct (tolower (sbyte (Znth i L1)) - tolower (sbyte (Znth i L2)) =? 0) eqn:Et.
      - apply Z.eqb_eq in Et. rewrite Et in *. contradiction.
      - simpl. rewrite (cstr_tschar sh1 s1), (cstr_tschar sh2 s2) by auto. fold L1 L2. entailer!. }
    assert (Et: tolower (sbyte (Znth i L1)) - tolower (sbyte (Znth i L2)) = 0).
    { first [lia | apply repr_inj_signed; try (unfold repable_signed; rep_lia); auto]. }
    rewrite Et in Heq. simpl in Heq.
    forward.
    unfold sv at 1.
    forward_if.
    { forward. apply (sbyte_inj _ 0) in H9; try lia.
      rewrite H9 in Heq. simpl in Heq. fold L1 L2. rewrite Heq. rewrite (cstr_tschar sh1 s1), (cstr_tschar sh2 s2) by auto. fold L1 L2. entailer!. }
    assert (Hn1: Znth i L1 <> 0) by (intro E; rewrite E in H9; auto).
    replace (Znth i L1 =? 0) with false in Heq by (symmetry; apply Z.eqb_neq; auto).
    assert (Hi1: i < Zlength s1).
    { destruct (Z.eq_dec i (Zlength s1)); [ | lia]. subst i. unfold L1 in Hn1. rewrite Znth_s0_end in Hn1. contradiction. }
    assert (Hi2: i < Zlength s2).
    { destruct (Z.eq_dec i (Zlength s2)); [ | lia]. subst i. unfold L2 in Et. rewrite Znth_s0_end in Et.
      change (tolower (sbyte 0)) with 0 in Et. rewrite Z.sub_0_r in Et. apply tolower_zero in Et; [contradiction | lia]. }
    forward. Exists (i + 1). entailer!.
  - forward. fold L1 L2. match goal with Hz: ncasecmp L1 L2 _ = 0 |- _ => rewrite Hz end. rewrite (cstr_tschar sh1 s1), (cstr_tschar sh2 s2) by auto. fold L1 L2. entailer!.
Qed.
