(* Piece 10 of the main of harness/x_a2ulabel.c: the loop that measures the string (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.

Lemma piece10 {Espec: OracleKind} gv v_k n bs pin psnap pcps:
  (forall sl, semax Delta_main (pre11 gv v_k n bs sl pin psnap pcps) (Ssequence T11 ret0) main_post) ->
  semax Delta_main (pre10 gv v_k n bs pin psnap pcps) (Ssequence T10 ret0) main_post.
Proof.
  intros H11. unfold pre10, T10, ret0, main_post, Delta_main. abbreviate_semax.
  assert_PROP (in_ok n bs) as Hin by entailer!.
  destruct Hin as (Hn & Hbs & Hlen).
  forward_loop (EX sl: Z,
    PROP (in_ok n bs; 0 <= sl <= n; Forall (fun b => b <> 0) (sublist 0 sl bs))
    LOCAL (temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
           temp _cps pcps; gvars gv; lvar _k t_sink v_k)
    SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         data_at_ Tsh t_sink v_k;
         data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
         data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
         data_at_ Ews (tarray tuint 512) pcps; TT))
  break: (EX sl: Z, pre11 gv v_k n bs sl pin psnap pcps).
  - Exists 0. entailer!.
  - Intros sl.
    assert (Hz: Znth sl (vb (bs ++ [0])) = Vint (Int.repr (Znth sl (bs ++ [0])))).
    { unfold vb. rewrite Znth_map; auto. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    assert (Hb: 0 <= Znth sl (bs ++ [0]) <= Byte.max_unsigned).
    { assert (Forall (fun b => 0 <= b <= Byte.max_unsigned) (bs ++ [0])).
      { apply Forall_app; split; auto. repeat constructor; rep_lia. }
      eapply Forall_forall in H2; [exact H2|]. apply Znth_In.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    forward.
    { entailer!. unfold vb; rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    unfold vb at 1; rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    forward_if.
    + forward. Exists (sl + 1). entailer!.
      rename H2 into Hnz.
      assert (sl < Zlength bs).
      { destruct (Z.eq_dec sl (Zlength bs)); [|lia]. subst sl.
        rewrite app_Znth2 in Hnz by lia. replace (Zlength bs - Zlength bs) with 0 in Hnz by lia.
        rewrite Znth_0_cons in Hnz. contradiction Hnz; reflexivity. }
      split; [lia|].
      rewrite (sublist_split 0 sl (sl+1)) by lia. apply Forall_app; split; auto.
      rewrite sublist_len_1 by lia. constructor; [|constructor].
      rewrite app_Znth1 in Hnz by lia. exact Hnz.
    + forward. Exists sl. unfold pre11, in_ok, sl_ok. entailer!.
  - Intros sl.
    eapply semax_pre; [ | apply (H11 sl) ].
    unfold pre11. entailer!.
Qed.
