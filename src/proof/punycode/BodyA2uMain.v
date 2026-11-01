(* The body of ossl_a2ulabel (crypto/punycode.c, patched), under Punycode.CS: the assembly of its pieces
   (A2uNull, A2uNonNull, A2uInit, A2uLabel, A2uPost; the assertions in A2uDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uNull.
Require Import OpensslPunycode.proof.punycode.A2uNonNull.
Require Import OpensslPunycode.proof.punycode.A2uInit.
Require Import OpensslPunycode.proof.punycode.A2uLabel.
Require Import OpensslPunycode.proof.punycode.A2uPost.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.

Lemma body_a2ulabel_proof : semax_body Vprog Gprog_a2ulabel f_ossl_a2ulabel ossl_a2ulabel_spec.
Proof.
  start_function.
  repeat match goal with P := @abbreviate statement _ |- _ => unfold abbreviate in P; subst P end.
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  destruct (Val.eq out nullval) as [Eo|Eo].
  { eapply a2u_null_ok; eauto. }
  eapply a2u_nonnull_ok; eauto; [destruct H1; [contradiction | auto] |].
  intros CTX.
  apply semax_seq with (EX sub: val, !! (fn = 0 /\ 0 < cap) &&
    a2u_inv gv shi pin s sho out cap init tk zf live sub v_buf v_pkt v_bufsize v_seed).
  { eapply semax_pre; [| apply a2u_init_ok; eauto].
    entailer!. }
  Intros sub. apply semax_extract_prop; intros [Fn0 Cp]. subst fn.
  apply semax_seq with (a2u_brk gv shi pin s sho out cap init tk zf live sub v_buf v_pkt v_bufsize v_seed).
  { apply semax_loop with (a2u_inv gv shi pin s sho out cap init tk zf live sub v_buf v_pkt v_bufsize v_seed).
    - apply a2u_label_ok; auto.
    - eapply semax_post_flipped; [apply semax_skip|..]; intros;
        apply andp_left2; first [apply derives_refl | apply FF_left]. }
  apply a2u_post_ok; auto.
  unfold shim_bounds in *. rep_lia.
Qed.
