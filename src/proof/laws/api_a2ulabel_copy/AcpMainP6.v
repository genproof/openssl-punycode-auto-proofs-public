(* The second piece of the main of harness/api_a2ulabel_copy.c (AcpMainDefs): `in[len] = 0`, then the loop that
   computes the string's length n (AcpStr: the octets of in before its first NUL). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_copy.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpStr.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainDefs.

Lemma piece6 {Espec: OracleKind} gv len bs0 pin outlen ob pout psaved:
  (forall s t, semax Delta_main (pre9 gv len s t pin outlen ob pout psaved) (Ssequence T9 ret0) main_post) ->
  semax Delta_main (pre6 gv len bs0 pin outlen ob pout psaved) (Ssequence T6 ret0) main_post.
Proof.
  intros HK. unfold pre6, T6, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  (* in[len] = 0 *)
  forward.
  set (bs := sublist 0 len bs0).
  assert (Hl: Zlength bs = len) by (subst bs; list_solve).
  assert (Hok: bytes_ok bs) by (subst bs; apply Forall_sublist; auto).
  replace (upd_Znth len (vb bs0) (Vint (Int.zero_ext 8 (Int.repr 0)))) with (vb (bs ++ [0])).
  2: { change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). subst bs. unfold vb. list_solve. }
  clearbody bs.
  pose proof (acp_first0_range bs) as Hf.
  (* n = 0; while (in[n] != 0) n++ *)
  forward.
  forward_loop (EX k: Z,
    PROP (0 <= k <= acp_first0 bs)
    LOCAL (temp _n (Vlong (Int64.repr k)); temp _saved psaved; temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
    SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin;
         data_at Ews (tarray tuchar outlen) (vb ob) pout;
         data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))
  break: (
    PROP ()
    LOCAL (temp _n (Vlong (Int64.repr (acp_first0 bs))); temp _saved psaved; temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
    SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin;
         data_at Ews (tarray tuchar outlen) (vb ob) pout;
         data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT)).
  { Exists 0. entailer!. }
  { Intros k.
    forward.
    { entailer!. unfold vb. rewrite Znth_map by list_solve. simpl.
      assert (0 <= Znth k (bs ++ [0]) <= 255).
      { assert (bytes_ok (bs ++ [0])) as Hb by (unfold bytes_ok; rewrite Forall_app; split; auto; repeat constructor; rep_lia).
        unfold bytes_ok in Hb. rewrite Forall_Znth in Hb. apply Hb. list_solve. }
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold vb at 1. rewrite Znth_map by list_solve.
    forward_if.
    { forward. Exists (k + 1). entailer!.
      destruct (Z.eq_dec k (acp_first0 bs)) as [E | E].
      - match goal with Hn: Int.repr (Znth _ _) <> _ |- _ => rewrite E, acp_first0_at in Hn; contradiction end.
      - lia. }
    { forward. entailer!.
      destruct (Z.eq_dec k (acp_first0 bs)) as [E | E]; [ rewrite E; reflexivity | exfalso ].
      apply (acp_first0_nz bs k); [ lia | ].
      assert (0 <= Znth k bs <= 255) by (unfold bytes_ok in Hok; rewrite Forall_Znth in Hok; apply Hok; lia).
      match goal with Hz: Int.repr (Znth _ _) = Int.repr 0 |- _ =>
        rewrite app_Znth1 in Hz by lia; apply repr_inj_unsigned in Hz; rep_lia end. } }
  eapply semax_pre;
    [ | apply (HK (sublist 0 (acp_first0 bs) bs) (sublist (acp_first0 bs + 1) (Zlength bs + 1) (bs ++ [0]))) ].
  unfold pre9. rewrite <- acp_first0_split.
  assert (bytes_ok (sublist (acp_first0 bs + 1) (Zlength bs + 1) (bs ++ [0]))).
  { apply Forall_sublist. unfold bytes_ok; rewrite Forall_app; split; auto; repeat constructor; rep_lia. }
  pose proof (acp_first0_str bs Hok).
  entailer!.
  list_solve.
Qed.
