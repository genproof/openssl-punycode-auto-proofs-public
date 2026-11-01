(* The body of CRYPTO_free (patch/shim/ossl_shim.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.
Require Import OpensslPunycode.proof.shim.ShimLemmas.

Local Open Scope logic.

Lemma body_CRYPTO_free_: semax_body Vprog Gprog_free f_CRYPTO_free CRYPTO_free_spec.
Proof.
  start_function.
  unfold shim_state. destruct H1 as (Hfn & Hzf & Hlive).
  destruct (eq_dec p nullval).
  - subst p. forward_if. { exfalso. first [discriminate | auto]. } forward. entailer!. unfold shim_state. cancel.
  - Intros. forward_if.
    + forward. forward.
      forward_call (tarray tuchar n, p, gv).
      { rewrite if_false by auto. cancel. }
      entailer!. unfold shim_state. cancel.
    + subst p. contradiction.
Qed.


