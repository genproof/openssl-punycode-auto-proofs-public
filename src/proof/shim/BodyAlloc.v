(* The body of CRYPTO_zalloc (patch/shim/ossl_shim.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.

Local Open Scope logic.

Lemma body_CRYPTO_zalloc_: semax_body Vprog Gprog_zalloc f_CRYPTO_zalloc CRYPTO_zalloc_spec.
Proof.
  start_function.
  unfold shim_state. destruct H1 as (Hfn & Hzf & Hlive). Intros.
  forward_if.
  { forward. forward. Exists nullval fn 1 live. unfold shim_state, zalloc_outcome.
    rewrite if_true by (apply (f_equal Int64.unsigned) in H1; rewrite Int64.unsigned_repr in H1 by rep_lia; auto).
    entailer!. }
  assert (Hn: num <> 0) by (intro; subst; auto).
  forward.
  forward_if (EX r: val, EX fn': Z,
     PROP (fn' = 0 /\ (fn <> 0 -> r = nullval))
     LOCAL (temp _ret r; gvars gv; temp _num (Vlong (Int64.repr num)))
     SEP (data_at Ews tint (Vint (Int.repr fn')) (gv _ossl_shim_fail_next);
          data_at Ews tint (Vint (Int.repr zf)) (gv _ossl_shim_zalloc_failed);
          data_at Ews tlong (Vlong (Int64.repr live)) (gv _ossl_shim_live); mem_mgr gv;
          if eq_dec r nullval then emp else malloc_token Ews (tarray tuchar num) r * data_at_ Ews (tarray tuchar num) r)).
  - forward. forward. Exists nullval 0. entailer!.
  - forward_call (tarray tuchar num, gv).
    { simpl. rewrite ?Z.max_r by lia. repeat split; auto; try rep_lia. }
    Intros r. forward. Exists r 0. entailer!.
  - Intros r fn'. subst fn'.
    match goal with Hq: fn <> 0 -> r = nullval |- _ => rename Hq into Hr end.
    destruct (eq_dec r nullval) as [Er | Er].
    + subst r. forward_if; [ | exfalso; auto].
      forward. forward. Exists nullval 0 1 live. unfold shim_state, zalloc_outcome.
      rewrite if_false by auto. entailer!. destruct (Z.eq_dec fn 0); auto.
    + Intros. forward_if; [exfalso; auto | ].
      forward_call (Ews, r, Zrepeat Vundef num, 0, num).
      { unfold arr0. rewrite if_false by auto. rewrite (QuickProof.Assembly.data_at_tuchar_cs _ CS). unfold data_at_, field_at_.
        simpl default_val. cancel. }
      { list_solve. }
      unfold arr0. rewrite if_false by auto. rewrite (QuickProof.Assembly.data_at_tuchar_cs _ CS).
      forward. forward. forward.
      Exists r 0 zf (live + 1). unfold shim_state, zalloc_outcome.
      assert (Hfn0: fn = 0) by (destruct (Z.eq_dec fn 0); auto; exfalso; auto).
      rewrite if_false by auto. rewrite if_true by auto.
      entailer!.
      rewrite if_false by auto. unfold zblock. change (0 mod 256) with 0. cancel.
Qed.
