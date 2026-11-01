(* The first piece of the main of harness/rj_a2ulabel_any.c: from the start of the body to the call of
   ossl_a2ulabel (JaaMainDefs): the input in and its copy saved, outlen, and out (NULL or any outlen octets). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rj_a2ulabel_any.code.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaProg.
Require Import OpensslPunycode.proof.laws.rj_a2ulabel_any.JaaMainDefs.

(* The result of any_bytes(outlen) as ossl_a2ulabel's out buffer (the token of a zero-size block kept as tk0's). *)
Lemma out_buf_of_any_bytes (cs1: compspecs) q n ob:
  (if eq_dec q nullval then emp
   else @malloc_token cs1 Ews (tarray tuchar n) q * @data_at cs1 Ews (tarray tuchar n) (vb ob) q)
  |-- OpensslPunycode.proof.punycode.PunySpec.out_buf Ews q n (vb ob) tk0 * TT.
Proof.
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  destruct (eq_dec q nullval) as [E | E].
  - rewrite if_true by auto. rewrite emp_sepcon. apply TT_right.
  - rewrite if_false by auto.
    rewrite (data_at_tuchar_cs cs1 OpensslPunycode.proof.punycode.PunySpec.CS).
    destruct (Z.eq_dec n 0) as [-> | N].
    + rewrite (@malloc_token_change_composite cs1 OpensslPunycode.proof.shim.ShimSpec.CS
                 (CCE_any cs1 OpensslPunycode.proof.shim.ShimSpec.CS) Ews (tarray tuchar 0)) by reflexivity.
      unfold tk0. cancel.
    + cancel.
Qed.

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

Lemma piece0 {Espec: OracleKind} gv:
  (forall len bs pin psaved outlen out ob,
     semax Delta_main (pre8 gv len bs pin psaved outlen out ob) (Ssequence T8 ret0) main_post) ->
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
Proof.
  intros HK. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  forward_call (Int64.max_signed - 1).
  Intros len.
  forward_call (len + 1, gv).
  Intros vret. destruct vret as [pin bs0]. simpl fst in *. simpl snd in *.
  Intros.
  (* if (in == NULL) return 0 *)
  forward_if (pin <> nullval).
  { destruct (eq_dec pin nullval); [ subst; entailer! | entailer! ]. }
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!. }
  Intros. rewrite if_false by auto. Intros.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.laws.common.HelperSpec.CS CS).
  (* in[len] = 0 *)
  forward.
  set (bs := sublist 0 len bs0).
  assert (Hl: Zlength (bs ++ [0]) = len + 1) by (subst bs; list_solve).
  assert (Hok: bytes_ok (bs ++ [0])).
  { unfold bytes_ok. rewrite Forall_app. split; [ apply Forall_sublist; auto | repeat constructor; rep_lia ]. }
  replace (upd_Znth len (vb bs0) (Vint (Int.zero_ext 8 (Int.repr 0)))) with (vb (bs ++ [0])).
  2: { change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). subst bs. unfold vb. list_solve. }
  (* saved = copy_of(in, len + 1): in is the block any_bytes gave (its token and its octets) *)
  gather_SEP (malloc_token _ _ pin) (data_at _ _ _ pin).
  replace_SEP 0 (if eq_dec pin nullval then emp
                 else (@malloc_token CCS Ews (tarray tuchar (Zlength (bs ++ [0]))) pin *
                       @data_at CCS Ews (tarray tuchar (Zlength (bs ++ [0]))) (vb (bs ++ [0])) pin)%logic).
  { rewrite if_false by auto. rewrite Hl.
    rewrite (data_at_tuchar_cs CS CCS). entailer!. }
  forward_call (Ews, pin, bs ++ [0], len + 1, gv).
  Intros psaved. rewrite !if_false by auto. rewrite Hl. Intros.
  replace (sublist 0 (len + 1) (bs ++ [0])) with (bs ++ [0]) by (rewrite sublist_same; auto).
  (* outlen = nondet_size(); out = nondet_u8() == 0 ? NULL : any_bytes(outlen) *)
  forward_call. Intros outlen.
  forward_call. Intros m.
  forward_if (EX out: val, EX ob: list Z,
    PROP (bytes_ok ob; Zlength ob = outlen)
    LOCAL (temp _t'6 out; temp _outlen (Vlong (Int64.repr outlen)); temp _saved psaved; temp _in pin;
           temp _len (Vlong (Int64.repr len)); gvars gv)
    SEP (mem_mgr gv; @data_at CCS Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin;
         if eq_dec psaved nullval then emp
         else @malloc_token CCS Ews (tarray tuchar (len + 1)) psaved *
              @data_at CCS Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) psaved;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
         OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         OpensslPunycode.proof.punycode.PunySpec.out_buf Ews out outlen (vb ob) tk0; TT)).
  { forward. Exists nullval (Zrepeat 0 outlen). entailer!.
    { split; [ unfold bytes_ok, Zrepeat; apply Forall_repeat; rep_lia | apply Zlength_Zrepeat; lia ]. } }
  { forward_call (outlen, gv).
    Intros vret. destruct vret as [q ob]. simpl fst in *. simpl snd in *.
    forward. Exists q ob. entailer!.
    sep_apply (out_buf_of_any_bytes OpensslPunycode.proof.laws.common.HelperSpec.CS q (Zlength ob) ob).
    cancel. }
  Intros out ob.
  forward.
  (* if (saved == NULL) return 0 *)
  forward_if (psaved <> nullval).
  { destruct (eq_dec psaved nullval); [ subst; entailer! | entailer! ]. }
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!. }
  Intros. rewrite if_false by auto. Intros.
  eapply semax_pre; [ | apply (HK len bs pin psaved outlen out ob) ].
  unfold pre8. rewrite !(data_at_tuchar_cs CCS CS).
  assert (Zlength bs = len) by (subst bs; list_solve).
  assert (bytes_ok bs) by (subst bs; apply Forall_sublist; auto).
  entailer!.
Qed.
