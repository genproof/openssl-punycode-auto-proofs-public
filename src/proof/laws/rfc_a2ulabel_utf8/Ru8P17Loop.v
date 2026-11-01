(* The utf8 loop of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainP17), for any outcome of the decoder: valid0 is
   the initial value of valid, cpsv the contents of cps, cnt that of count; when valid0 holds, the first cnt elements
   of cps are the code points out and ru8_want s is their UTF-8 form if none is above 0x10FFFF; else ru8_want s is
   None.  The loop writes the octets of out one code point at a time at want + size, stops (valid = 0) at the first
   code point above 0x10FFFF; then want[size] = 0, size++. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Lib.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Defs.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Put.
Local Open Scope logic.

Lemma ru8p17_loop {Espec: OracleKind} gv vc len s pl pc outlen ob pout psaved pw (v0: bool) cpsv cnt out:
  piece20_stmt ->
  0 <= cnt <= 512 -> Zlength cpsv = 512 ->
  (v0 = true -> Zlength out = cnt /\ sublist 0 cnt cpsv = vb out /\
                Forall (fun c => 0 <= c <= Int.max_unsigned) out /\
                ru8_want s = if forallb (fun c => c <=? 1114111) out then Some (concat (map utf8 out)) else None) ->
  (v0 = false -> ru8_want s = None) ->
  semax Delta_main
  (PROP (0 <= len <= Int64.max_signed - 5; Zlength s = len; bytes_ok s;
        Forall (fun c => c <> 46 /\ c <> 0) s;
        1 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout <> nullval)
  LOCAL (temp _size (Vlong (Int64.repr 0)); temp _valid (Vint (Int.repr (if v0 then 1 else 0)));
         temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) cpsv pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at Tsh tuint (Vint (Int.repr cnt)) vc; mem_mgr gv;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT))
  (Ssequence T17 ret0) main_post.
Proof.
  intros Hnext Hcnt Hcps HT HF.
  unfold T17, ret0, main_post. abbreviate_semax.
  Intros.
  forward.
  forward_loop
    (EX j: Z, EX v: bool, EX sz: Z, EX wv: list val,
     PROP (0 <= j <= cnt; 0 <= sz <= 4 * j; Zlength wv = 2049; ru8p17_ok s out v0 v j sz wv)
     LOCAL (temp _j (Vint (Int.repr j)); temp _size (Vlong (Int64.repr sz));
            temp _valid (Vint (Int.repr (if v then 1 else 0)));
            temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
            temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
     SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
          data_at Ews (tarray tuint 512) cpsv pc;
          data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
          data_at Ews (tarray tuchar 2049) wv pw;
          data_at Tsh tuint (Vint (Int.repr cnt)) vc; mem_mgr gv;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
          OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
          TT))
  continue:
    (EX j: Z, EX v: bool, EX sz: Z, EX wv: list val,
     PROP (0 <= j < cnt; 0 <= sz <= 4 * (j + 1); Zlength wv = 2049; ru8p17_ok s out v0 v (j + 1) sz wv)
     LOCAL (temp _j (Vint (Int.repr j)); temp _size (Vlong (Int64.repr sz));
            temp _valid (Vint (Int.repr (if v then 1 else 0)));
            temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
            temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
     SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
          data_at Ews (tarray tuint 512) cpsv pc;
          data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
          data_at Ews (tarray tuchar 2049) wv pw;
          data_at Tsh tuint (Vint (Int.repr cnt)) vc; mem_mgr gv;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
          OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
          TT))
  break:
    (EX v: bool, EX sz: Z, EX wv: list val,
     PROP (0 <= sz <= 2048; Zlength wv = 2049;
           if v then ru8_want s = Some (concat (map utf8 out)) /\ sz = Zlength (concat (map utf8 out)) /\
                     wv = vb (concat (map utf8 out)) ++ Zrepeat Vundef (2049 - sz)
           else ru8_want s = None)
     LOCAL (temp _size (Vlong (Int64.repr sz));
            temp _valid (Vint (Int.repr (if v then 1 else 0)));
            temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
            temp _label pl; gvars gv; lvar _count tuint vc)
     SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
          data_at Ews (tarray tuint 512) cpsv pc;
          data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
          data_at Ews (tarray tuchar 2049) wv pw;
          data_at Tsh tuint (Vint (Int.repr cnt)) vc; mem_mgr gv;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
          OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
          TT)).
  - (* entry *)
    Exists 0 v0 0 (Zrepeat Vundef 2049). entailer!.
    unfold ru8p17_ok. destruct v0; [|auto].
    unfold ru8p17_w. rewrite sublist_nil. simpl. auto.
  - (* the body *)
    Intros j v sz wv.
    forward_if (temp _t'15 (Vint (Int.repr (if v then (if j <? cnt then 1 else 0) else 0)))).
    { forward. forward. entailer!. destruct v; [|contradiction].
      destruct (zlt j cnt), (Z.ltb_spec j cnt); try lia; reflexivity. }
    { forward. entailer!. destruct v; [discriminate|reflexivity]. }
    forward_if.
    2: { (* the end: valid = 0, or every code point done *)
      forward. Exists v sz wv. entailer!.
      unfold ru8p17_ok in H10. destruct v; [|exact H10].
      destruct H10 as [-> [Hok [Hsz Hwv]]]. destruct (HT eq_refl) as [Hl [_ [_ Hw]]].
      destruct (Z.ltb_spec j cnt); [inversion H11|].
      assert (j = Zlength out) by lia. subst j. unfold ru8p17_w in *.
      rewrite sublist_same in * by lia. rewrite ru8p17_forallb in Hw by auto. auto. }
    (* valid and j < count: the code point c = cps[j] *)
    destruct v; [|contradiction].
    destruct (Z.ltb_spec j cnt); [|contradiction].
    unfold ru8p17_ok in H10. destruct H10 as [-> [Hok [Hsz Hwv]]]. destruct (HT eq_refl) as [Hl [Hpre [Hrng Hw]]].
    assert (Znth j cpsv = Vint (Int.repr (Znth j out))) as Hj.
    { replace (Znth j cpsv) with (Znth j (sublist 0 cnt cpsv)) by (rewrite Znth_sublist by lia; f_equal; lia).
      rewrite Hpre. unfold vb. rewrite Znth_map by lia. reflexivity. }
    assert (0 <= Znth j out <= Int.max_unsigned) as Hc
      by (rewrite Forall_forall in Hrng; apply Hrng; apply Znth_In; lia).
    forward.
    { entailer!. fixZ. rewrite Hj. simpl. auto. }
    fixZ. rewrite Hj.
    forward_if.
    { (* c > 0x10FFFF: valid = 0 *)
      forward. Exists j false sz wv. entailer!.
      unfold ru8p17_ok. rewrite Hw, (ru8p17_forallb_false out j) by lia. auto. }
    (* c <= 0x10FFFF: its octets at want + size *)
    apply (ru8p17_put_ok gv vc len s pl pc outlen ob pout psaved pw cpsv cnt out j sz wv); auto; lia.
  - (* j++ *)
    Intros j v sz wv.
    forward.
    Exists (j + 1) v sz wv. entailer!.
  - (* after the loop *)
    Intros v sz wv.
    forward. forward.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS; subst POSTCONDITION MORE_COMMANDS.
    eapply semax_pre;
      [ | apply (Hnext Espec gv vc len s pl outlen ob pout psaved pw (sz + 1)
                   (upd_Znth sz wv (Vint (Int.zero_ext 8 (Int.repr 0))))) ].
    unfold pre20.
    destruct v.
    + destruct H9 as [Hw [Hsz Hwv]]. rewrite Hw. entailer!.
      unfold vb. rewrite map_app. simpl. list_solve.
    + rewrite H9. entailer!.
Qed.
