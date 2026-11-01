(* The tail of one iteration of the loop of MainLoop1.v (one_label and ulen updated for the code point c just
   picked), cut out to keep MainLoop1.v under the time budget. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs.

Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLoop1A.
Local Open Scope logic.

(* The loop body after gp_assume(cps[j] <= 1114111): a sub-term of stmt_loop1. *)
Definition stmt_loop1_rest : statement :=
  match stmt_loop1 with
  | Ssequence (Ssequence _ (Sloop (Ssequence _ (Ssequence _ (Ssequence _ s))) _)) _ => s
  | _ => Sskip
  end.

Lemma loop1_rest: forall (Espec: OracleKind) gv m pc vo ve i pre c,
  0 <= m <= 512 -> 0 <= i < m -> Zlength pre = i -> Forall (fun c => 0 <= c <= 1114111) pre ->
  0 <= c <= 1114111 ->
  semax Delta_main
    (PROP ()
     LOCAL (temp _t'33 (Vint (Int.repr c)); temp _j (Vlong (Int64.repr i));
            temp _ulen (Vlong (Int64.repr (ulen_of pre)));
            temp _one_label (Vint (Int.repr (if one_label_ok pre then 1 else 0)));
            temp _cps pc; temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
     SEP (data_at Ews (tarray tuint m) (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))%Z) pc;
          data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
          OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
          OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT))
    stmt_loop1_rest
    (normal_ret_assert
       (EX pre0 : list Z,
        PROP (Zlength pre0 = (i + 1)%Z; Forall (fun c0 : Z => 0 <= c0 <= 1114111) pre0)
        LOCAL (temp _j (Vlong (Int64.repr i)); temp _ulen (Vlong (Int64.repr (ulen_of pre0)));
               temp _one_label (Vint (Int.repr (if one_label_ok pre0 then 1 else 0)));
               temp _cps pc; temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
        SEP (arr0 Ews tuint m (vb pre0 ++ Zrepeat Vundef (m - (i + 1))%Z) pc;
             data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
             OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
             OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT))%argsassert).
Proof.
  intros Espec gv m pc vo ve i pre c H0 H1 H2 H3 [Hc0 Hc2].
  unfold stmt_loop1_rest, stmt_loop1. cbv iota. abbreviate_semax.
  assert (Hz: forall d: Inhabitant val, @Znth val d i (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))) = Vint (Int.repr c)).
  { intros d. rewrite app_Znth1 by (unfold vb; rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil; lia).
    unfold vb. rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite app_Znth2 by lia. rewrite H2, Z.sub_diag. reflexivity. }
  forward.
  { entailer!. rewrite Hz. exact I. }
  rewrite Hz.
  forward_if (PROP ()
    LOCAL (temp _t'4 (Vint (Int.repr (if ((c =? 46) || (c =? 0))%bool then 1 else 0)));
           temp _j (Vlong (Int64.repr i)); temp _ulen (Vlong (Int64.repr (ulen_of pre)));
           temp _one_label (Vint (Int.repr (if one_label_ok pre then 1 else 0)));
           temp _cps pc; temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (data_at Ews (tarray tuint m) (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))) pc;
        data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
        OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
        OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT)).
  { forward. entailer!. }
  { forward. { entailer!. rewrite Hz. exact I. } rewrite Hz. forward. entailer!.
    rewrite (proj2 (Z.eqb_neq c 46) ltac:(assumption)). simpl.
    destruct (zeq c 0) as [->|E0]; [reflexivity | rewrite (proj2 (Z.eqb_neq c 0) E0); reflexivity]. }
  forward_if (PROP ()
    LOCAL (temp _j (Vlong (Int64.repr i)); temp _ulen (Vlong (Int64.repr (ulen_of pre)));
           temp _one_label (Vint (Int.repr (if one_label_ok (pre ++ [c]) then 1 else 0)));
           temp _cps pc; temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (data_at Ews (tarray tuint m) (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))) pc;
        data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
        OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
        OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT)).
  { forward. entailer!.
    rewrite loop1_one_label_snoc; destruct (c =? 46), (c =? 0); simpl in *; rewrite ?andb_true_r, ?andb_false_r;
      try reflexivity; match goal with Hx: ?a <> ?a |- _ => exfalso; apply Hx; reflexivity end. }
  { forward. entailer!.
    rewrite loop1_one_label_snoc; destruct (c =? 46), (c =? 0); simpl in *; rewrite ?andb_true_r, ?andb_false_r;
      try reflexivity; match goal with Hx: Int.repr _ = Int.zero |- _ => inversion Hx end. }
  pose proof (loop1_ulen_bounds pre) as Hub.
  pose proof (loop1_ulen_snoc pre c ltac:(lia)) as Hus.
  forward.
  { entailer!. rewrite Hz. exact I. }
  rewrite Hz.
  forward_if (PROP ()
    LOCAL (temp _j (Vlong (Int64.repr i)); temp _ulen (Vlong (Int64.repr (ulen_of (pre ++ [c]))));
           temp _one_label (Vint (Int.repr (if one_label_ok (pre ++ [c]) then 1 else 0)));
           temp _cps pc; temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (data_at Ews (tarray tuint m) (vb (pre ++ [c]) ++ Zrepeat Vundef (m - (i + 1))) pc;
        data_at_ Tsh tuint vo; data_at_ Tsh tulong ve;
        OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
        OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT)).
  { forward. entailer!. rewrite Hus; destruct (Z.ltb_spec c 128); [|destruct (Z.ltb_spec c 2048); [|destruct (Z.ltb_spec c 65536)]]; try lia; reflexivity. }
  { forward. { entailer!. rewrite Hz. exact I. } rewrite Hz.
    forward_if.
    { forward. entailer!. rewrite Hus; destruct (Z.ltb_spec c 128); [|destruct (Z.ltb_spec c 2048); [|destruct (Z.ltb_spec c 65536)]]; try lia; reflexivity. }
    forward. { entailer!. rewrite Hz. exact I. } rewrite Hz.
    forward_if.
    { forward. entailer!. rewrite Hus; destruct (Z.ltb_spec c 128); [|destruct (Z.ltb_spec c 2048); [|destruct (Z.ltb_spec c 65536)]]; try lia; reflexivity. }
    { forward. entailer!. rewrite Hus; destruct (Z.ltb_spec c 128); [|destruct (Z.ltb_spec c 2048); [|destruct (Z.ltb_spec c 65536)]]; try lia; reflexivity. } }
  Exists (pre ++ [c]). entailer!.
  + split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | apply Forall_app; split; auto].
  + unfold arr0. rewrite if_false by lia. cancel.
Qed.
