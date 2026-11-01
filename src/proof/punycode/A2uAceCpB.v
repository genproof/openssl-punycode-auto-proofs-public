(* ossl_a2ulabel, ACE branch, code-point loop body, part B: if (utfsize == 0) { result = -1; break; }. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uAceRange.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uAceDefs.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.
Lemma cpb_utf8_len: forall c, 0 <= Zlength (utf8 c) <= 4.
Proof.
  intros. unfold utf8.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma cp_b_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh Inv R,
  a2u_ctx shi pin s sho out cap init -> cps_ok cps bv ->
  semax DeltaA
    (cp_a gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh)
    s_cpb
    (overridePost (cp_b gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh)
       (loop1_ret_assert Inv (overridePost (cp_brk gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv) R))).
Proof.
  intros. unfold cp_a, cp_b, s_cpb. abbreviate_semax.
  Intros new.
  pose proof (cpb_utf8_len (Znth i cps)) as HL.
  forward_if.
  - forward. forward.
    assert (E: Zlength (utf8 (Znth i cps)) = 0).
    { apply (f_equal Int64.unsigned) in H5. rewrite Int64.unsigned_repr in H5 by rep_lia. exact H5. }
    destruct H0 as [_ [? ?]].
    assert (P: put_utf8s cap (w0, sh0) cps = (false, (w, sh))).
    { rewrite H2, put_utf8s_next by lia. rewrite E. reflexivity. }
    unfold loop1_ret_assert; destruct R; cbv beta iota; cbn [tycontext.RA_break].
    unfold cp_brk. Exists w sh (-1) new. entailer!.
  - unfold loop1_ret_assert; destruct R; cbv beta iota; cbn [tycontext.RA_normal].
    forward. unfold cp_a. Exists new. entailer!.
    destruct (Z.eq_dec (Zlength (utf8 (Znth i cps))) 0) as [E|E]; [rewrite E in H5; contradiction|lia].
Qed.
