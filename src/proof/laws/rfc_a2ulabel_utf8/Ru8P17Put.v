(* One turn of the utf8 loop of the main of harness/rfc_a2ulabel_utf8.c (Ru8P17Loop) for a code point c = cps[j]
   at most 0x10FFFF while valid: want is cut at size and size + |utf8 c| (at most 4 octets: size + 4 <= 2049 since
   size <= 4 j and j < count <= 512), utf8 writes the octets of c there, and size grows by their number. *)
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
Local Open Scope logic.

Lemma ru8p17_put_ok {Espec: OracleKind} gv vc len s pl pc outlen ob pout psaved pw cpsv cnt out j sz wv:
  0 <= cnt <= 512 -> 0 <= j < cnt -> Zlength out = cnt -> 0 <= sz <= 4 * j -> Zlength wv = 2049 ->
  Forall (fun c => c <= 1114111) (sublist 0 j out) -> sz = Zlength (ru8p17_w out j) ->
  wv = vb (ru8p17_w out j) ++ Zrepeat Vundef (2049 - sz) ->
  Znth j cpsv = Vint (Int.repr (Znth j out)) -> 0 <= Znth j out <= Int.max_unsigned -> 1114111 >= Znth j out ->
  semax Delta_main
  (PROP ()
   LOCAL (temp _t'23 (Vint (Int.repr (Znth j out))); temp _t'15 (Vint (Int.repr 1)); temp _j (Vint (Int.repr j));
          temp _size (Vlong (Int64.repr sz)); temp _valid (Vint (Int.repr 1));
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
  ru8p17_put
  (normal_ret_assert (ru8p17_inc gv vc len s pl pc outlen ob pout psaved pw true cpsv cnt out)).
Proof.
  intros Hcnt Hjc Hl H8 H9 Hok Hsz Hwv Hj Hc H10.
  unfold ru8p17_put, ru8p17_inc. abbreviate_semax.
  forward.
  { entailer!. fixZ. rewrite Hj. simpl. auto. }
  fixZ. rewrite Hj.
  set (c := Znth j out) in *.
  set (W := ru8p17_w out j) in *.
  pose proof (ru8p17_utf8_len c) as HL.
  set (L := Zlength (utf8 c)) in *.
  assert (Zlength (vb W) = sz) as HW by (rewrite Zlength_vb; auto).
  assert_PROP (field_compatible (tarray tuchar 2049) [] pw) as Hfc by entailer!.
  rewrite (ru8p17_split3 Ews 2049 sz L wv pw) by first [exact Hfc | lia]. Intros.
  forward_call (c, Ews, offset_val sz pw, sublist sz (sz + L) wv).
  { rewrite Zlength_sublist by lia. lia. }
  forward.
  set (wv' := vb (W ++ utf8 c) ++ Zrepeat Vundef (2049 - (sz + L))).
  Exists j true (sz + L) wv'.
  assert (Zlength wv' = 2049) as Hwv' by (subst wv'; rewrite Zlength_app, Zlength_vb, Zlength_app, Zlength_Zrepeat; lia).
  rewrite (ru8p17_split3 Ews 2049 sz L wv' pw) by first [exact Hfc | lia].
  replace (sublist 0 sz wv') with (sublist 0 sz wv) by (subst wv' wv; unfold vb; rewrite map_app; list_solve).
  replace (sublist sz (sz + L) wv') with (vb (utf8 c)) by (subst wv'; unfold vb; rewrite map_app; list_solve).
  replace (sublist (sz + L) 2049 wv') with (sublist (sz + L) 2049 wv) by (subst wv' wv; unfold vb; rewrite map_app; list_solve).
  entailer!.
  split; [lia|]. unfold ru8p17_ok.
  assert (ru8p17_w out (j + 1) = W ++ utf8 c) as HW1
    by (unfold ru8p17_w at 1; rewrite ru8p17_concat_step by lia; reflexivity).
  rewrite HW1. split; [|split].
  + rewrite (sublist_split 0 j (j + 1)) by lia. apply Forall_app. split; auto.
    rewrite sublist_len_1 by lia. constructor; [change (Znth j out) with c; lia | constructor].
  + rewrite Zlength_app. reflexivity.
  + reflexivity.
Qed.
