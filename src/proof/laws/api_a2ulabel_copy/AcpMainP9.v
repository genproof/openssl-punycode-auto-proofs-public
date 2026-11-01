(* The third piece of the main of harness/api_a2ulabel_copy.c (AcpMainDefs): the gp_assume loop over the positions
   of the string s that start a label; after it, no label of s starts with "xn--" in any case (acp_noprefix). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_copy.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainDefs.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainP9b.

Lemma piece9 {Espec: OracleKind} gv len s t pin outlen ob pout psaved:
  semax Delta_main (pre10 gv len s t pin outlen ob pout psaved) (Ssequence T10 ret0) main_post ->
  semax Delta_main (pre9 gv len s t pin outlen ob pout psaved) (Ssequence T9 ret0) main_post.
Proof.
  intros. unfold pre9, T9, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  forward.
  forward_loop
    (EX i: Z,
     PROP (0 <= i <= Z.max 0 (Zlength s - 3); acp_upto s i)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr (Zlength s))); temp _saved psaved;
            temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
     SEP (mem_mgr gv; PunySpec.puny_consts gv; PunySpec.xn_lit gv; ShimSpec.shim_state gv 0 0 0;
          data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
          data_at Ews (tarray tuchar outlen) (vb ob) pout;
          data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))
  continue:
    (EX i: Z,
     PROP (0 <= i; i + 3 < Zlength s; acp_upto s (i + 1))
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr (Zlength s))); temp _saved psaved;
            temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
     SEP (mem_mgr gv; PunySpec.puny_consts gv; PunySpec.xn_lit gv; ShimSpec.shim_state gv 0 0 0;
          data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
          data_at Ews (tarray tuchar outlen) (vb ob) pout;
          data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))
  break: (pre10 gv len s t pin outlen ob pout psaved).
  { Exists 0. entailer!. apply acp_upto_0. }
  { Intros i.
    pose proof (Zlength_nonneg s); pose proof (Zlength_nonneg t).
    assert (Hi: i <= Zlength s)
      by (destruct (Z.max_spec 0 (Zlength s - 3)) as [[? E] | [? E]]; rewrite E in H7; lia).
    forward_if.
    2:{ forward. rewrite add64_repr in H11; rewrite !Int64.unsigned_repr in H11 by rep_lia.
        unfold pre10. entailer!. apply (acp_upto_noprefix s i); auto. lia. }
    assert (Hi3: i + 3 < Zlength s)
      by (rewrite add64_repr in H11; rewrite !Int64.unsigned_repr in H11 by rep_lia; lia).
    clear H11.
    forward_if (temp _t'13 (Vint (Int.repr (if orb (i =? 0) (Znth (i - 1) s =? 46) then 1 else 0)))).
    { apply repr_inj_unsigned64 in H11; [ | rep_lia | rep_lia ]. subst i. forward. entailer!. }
    { assert (i <> 0) by (intro; subst; contradiction). forward.
      { entailer!. acp_rd. pose proof (acp_byte s (i - 1) H1 ltac:(lia)). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      acp_rd. forward. entailer!. replace (i =? 0) with false by lia.
      rewrite acp_eqb by (pose proof (acp_byte s (i - 1) H1 ltac:(lia)); lia). reflexivity. }
    forward_if.
    2:{ forward. Exists i. entailer!. apply acp_upto_skip; auto.
        destruct (orb (i =? 0) (Znth (i - 1) s =? 46)) eqn:E; [ discriminate | ].
        rewrite orb_false_iff, !Z.eqb_neq in E. tauto. }
    apply (acp_check gv len s t pin outlen ob pout psaved i); auto; lia. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  unfold MORE_COMMANDS, POSTCONDITION, Delta, Delta_specs, abbreviate. exact H.
Qed.