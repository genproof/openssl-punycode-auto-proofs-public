(* The body of any_bytes (harness/laws_common.h): malloc(n), then n arbitrary octets written by nondet_bytes when
   malloc did not fail (the block is non-NULL even when n = 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Lemma body_any_bytes : semax_body Vprog Gprog_any_bytes f_any_bytes any_bytes_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl; rep_lia. }
  Intros p.
  forward_if (EX bs: list Z,
    PROP (Zlength bs = n; bytes_ok bs)
    LOCAL (temp _bytes p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (vb bs) p)).
  { apply derives_trans with ((if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p *
      data_at_ Ews (tarray tuchar n) p) * TT)%logic; [ cancel | apply cmn_malloc_tc_test0; simpl; rep_lia ]. }
  - rewrite if_false by auto. Intros.
    forward_call (p, n, Ews).
    { rewrite if_false by auto. cancel. }
    Intros bs. rewrite if_false by auto.
    Exists bs. rewrite if_false by auto. entailer!.
  - forward. subst p. Exists (Zrepeat 0 n). rewrite if_true by auto.
    entailer!. split.
    + apply Zlength_Zrepeat. lia.
    + unfold bytes_ok. apply Forall_forall. intros x Hx. unfold Zrepeat in Hx. apply repeat_spec in Hx. subst x. rep_lia.
  - Intros bs. forward. Exists p bs. entailer!.
Qed.
