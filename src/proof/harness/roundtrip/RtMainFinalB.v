(* piece_final (MainFinal.v): the tail after ossl_a2ulabel succeeded (r2 = 1, u = the UTF-8 form and its NUL).
  *)
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib.

(* The tail of stmt_lab_final after r2 = ossl_a2ulabel(..): the check of r2 and of u, then of live. *)
Definition stmt_final_tail : statement :=
(Ssequence (Ssequence (Sset _t'20 (Evar _ossl_shim_zalloc_failed tint)) (Sifthenelse (Ebinop Oeq (Etempvar _t'20 tint) (Econst_int (Int.repr 0) tint) tint) (Ssequence (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default)) ((Ebinop Oeq (Etempvar _r2 tint) (Econst_int (Int.repr 1) tint) tint) :: nil)) (Ssequence (Scall (Some _t'18) (Evar _same_bytes (Tfunction ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tint cc_default)) ((Etempvar _u (tptr tuchar)) :: (Etempvar _want (tptr tuchar)) :: (Etempvar _ulen tulong) :: nil)) (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default)) ((Etempvar _t'18 tint) :: nil)))) (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default)) ((Ebinop Oeq (Etempvar _r2 tint) (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint) :: nil)))) (Ssequence (Sset _t'19 (Evar _ossl_shim_live tlong)) (Scall None (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default)) ((Ebinop Oeq (Etempvar _t'19 tlong) (Econst_int (Int.repr 0) tint) tint) :: nil)))).

Lemma data_at_arr0_nz (cs1 cs2: compspecs) sh n v p:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v p = @arr0 cs2 sh tuchar n v p.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma final_tail_ok {Espec: OracleKind} gv cps e plab pu pw vo ve:
  isptr pu -> 1 <= ulen_of cps <= 2049 -> bytes_ok (utf8s cps) ->
  semax Delta_main
   (PROP ( )
    LOCAL (temp _r2 (Vint (Int.repr 1)); temp _at (Vlong (Int64.repr (Zlength (utf8s cps)))); temp _want pw;
           temp _u pu; temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps))); gvars gv;
           lvar _olen tuint vo; lvar _elen tulong ve)
    SEP (OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
         OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv;
         OpensslPunycode.proof.shim.ShimSpec.cstr Ews (ace e) plab;
         OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pu (ulen_of cps) (vb (utf8s cps ++ [0])) (tarray tuchar 0);
         data_at Ews (tarray tuchar (ulen_of cps)) (vb (utf8s cps ++ [0])) pw;
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve; TT))
   stmt_final_tail (normal_ret_assert (Q_ret vo ve)).
Proof.
  intros Hpu Hul Hu8.
  unfold stmt_final_tail. abbreviate_semax.
  unfold OpensslPunycode.proof.shim.ShimSpec.shim_state.
  rewrite !(data_at_cs_tint OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite !(data_at_cs_tlong OpensslPunycode.proof.shim.ShimSpec.CS CS).
  Intros.
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf, OpensslPunycode.proof.shim.ShimSpec.zero_tok.
  destruct pu; try contradiction. rewrite if_false by discriminate. rewrite if_false by lia.
  rewrite sepcon_emp.
  assert (Eu: Zlength (utf8s cps ++ [0]) = ulen_of cps) by (unfold ulen_of; list_solve).
  rewrite <- Eu.
  rewrite (data_at_arr0_nz OpensslPunycode.proof.punycode.PunySpec.CS OpensslPunycode.proof.harness.RefRt.CS
    Ews (Zlength (utf8s cps ++ [0])) _ (Vptr b i)) by lia.
  rewrite (data_at_arr0_nz CS OpensslPunycode.proof.harness.RefRt.CS
    Ews (Zlength (utf8s cps ++ [0])) _ pw) by lia.
  assert (Hok: bytes_ok (utf8s cps ++ [0])).
  { unfold bytes_ok in *. rewrite Forall_app. split; auto. repeat constructor; rep_lia. }
  forward.
  forward_if True.
  { forward_call.
    forward_call (Ews, Vptr b i, utf8s cps ++ [0], Ews, pw, utf8s cps ++ [0]).
    rewrite if_true by reflexivity.
    forward_call.
    entailer!. }
  { first [ discriminate | contradiction ]. }
  forward. forward_call. unfold Q_ret. entailer!.
Qed.
