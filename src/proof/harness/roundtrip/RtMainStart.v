(* The start of the main of harness/x_roundtrip.c after the globals: m, cps, up to the first loop (MainLoop1.v).
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainDefs OpensslPunycode.proof.harness.roundtrip.RtMainLib.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainGlob.

(* main's body without its final (dead) return 0. *)
Definition stmt_main : statement :=
  ltac:(let b := eval cbv [f_main fn_body] in (fn_body f_main) in match b with Ssequence ?x _ => exact x end).

(* After the globals: the two locals, main_frame. *)
Definition P_start (gv: globals) (vo ve: val) : environ -> mpred :=
  PROPx [] (LOCALx [gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at_ Tsh tuint vo :: data_at_ Tsh tulong ve :: main_frame gv))).

Lemma piece_start: piece_loop1_stmt ->
  forall (Espec: OracleKind) gv vo ve, semax Delta_main (P_start gv vo ve) stmt_main main_ret.
Proof.
intros L1 Espec gv v_olen v_elen.
unfold P_start, stmt_main, main_ret, main_post. abbreviate_semax.
unfold main_frame.
forward_call tt.
Intros m.
forward_call (Int.repr (Z.b2z (negb (Int64.ltu (Int64.repr 512) (Int64.repr m))))).
assert (Hm: m <= 512).
{ unfold Int64.ltu in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
  destruct (zlt 512 m); [ contradiction H0; reflexivity | lia ]. }
clear H0.
forward_call (tarray tuint m, gv).
{ entailer!. simpl. rewrite Z.max_r by lia. rewrite Z.mul_comm. reflexivity. }
{ simpl. rewrite Z.max_r by lia. rep_lia. }
Intros pc.
forward_if (temp _t'3 (Vint (Int.repr (if eq_dec pc nullval then (if m =? 0 then 0 else 1) else 0)))).
{ eapply derives_trans; [ | apply (malloc_tc_test (tarray tuint m) pc TT) ]; [ cancel | simpl; rep_lia ]. }
{ forward. entailer!.
  rewrite if_true by auto. unfold Int64.cmpu. destruct (Z.eqb_spec m 0);
    [subst; reflexivity | rewrite Int64.eq_false; [reflexivity | intro E; apply repr_inj_unsigned64 in E; rep_lia]]. }
{ forward. entailer!. rewrite if_false by auto. reflexivity. }
forward_if.
{ forward. Exists (Int.repr 0). entailer!. }
forward. forward.
assert (Hpc: pc <> nullval \/ m = 0).
{ destruct (EqDec_val pc nullval); [ right | left; auto ].
  destruct (Z.eqb_spec m 0); auto. exfalso; apply Int.one_not_zero; exact H0. }
clear H0.
unfold MORE_COMMANDS, abbreviate.
eapply semax_pre; [ | apply (L1 Espec gv m pc v_olen v_elen) ].
sep_apply (malloc_arr0_tuint m pc ltac:(lia) Hpc).
unfold P_loop1, main_frame. entailer!.
Qed.
