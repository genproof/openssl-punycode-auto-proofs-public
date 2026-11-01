(* A piece of the main of harness/x_roundtrip.c (see MainDefs.v). *)
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainMallocsA OpensslPunycode.proof.harness.roundtrip.RtMainMallocsB.

Ltac nz_cases :=
  repeat match goal with
  | |- context [nz ?p ?n] => let E := fresh "E" in destruct (nz_01 p n) as [E | E]; rewrite E in *; clear E
  | H: context [nz ?p ?n] |- _ => let E := fresh "E" in destruct (nz_01 p n) as [E | E]; rewrite E in *; clear E
  end; simpl; try reflexivity; try contradiction;
  try match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H end.

Lemma piece_mallocs : decode_encode_stmt -> encode_chars_stmt -> piece_if_stmt -> piece_mallocs_stmt.
Proof.
intros DE EC HIF. unfold piece_mallocs_stmt. intros.
unfold P_mallocs, stmt_mallocs, main_frame, main_ret, main_post. abbreviate_semax.
Intros.
assert (Hbe: bytes_ok e) by (eapply enc_bytes_ok; eauto).
forward.
assert (He0 := Zlength_nonneg e). assert (Hm0 := Zlength_nonneg cps).
forward_call (tarray tuchar (Zlength e), gv).
{ simpl. rewrite Z.max_r by lia. rep_lia. }
Intros penc. forward.
forward_call (tarray tuint (Zlength cps), gv).
{ entailer!. simpl. rewrite Z.max_r by lia. rewrite Z.mul_comm. reflexivity. }
{ simpl. rewrite Z.max_r by lia. rep_lia. }
Intros pout.
change (if eq_dec penc nullval then emp else (malloc_token Ews (tarray tuchar (Zlength e)) penc *
  data_at_ Ews (tarray tuchar (Zlength e)) penc)%logic) with (mblock (tarray tuchar (Zlength e)) penc).
change (if eq_dec pout nullval then emp else (malloc_token Ews (tarray tuint (Zlength cps)) pout *
  data_at_ Ews (tarray tuint (Zlength cps)) pout)%logic) with (mblock (tarray tuint (Zlength cps)) pout).
freeze FR := (data_at Ews (tarray tuchar _) _ plab) (arr0 _ _ _ _ pc) (data_at_ _ _ vo) (PunySpec.puny_consts _)
  (PunySpec.xn_lit _) (ShimSpec.shim_state _ _ _ _) (mem_mgr _).
forward_if (temp _t'9 (Vint (Int.repr (nz penc (Zlength e))))).
{ eapply derives_trans; [ | apply (mblock_tc (tarray tuchar (Zlength e)) penc TT) ]; [ cancel | simpl; rep_lia ]. }
{ forward. forward. entailer!. symmetry; apply nz_null; rep_lia. }
{ forward. entailer!. rewrite nz_nonnull by auto. reflexivity. }
forward_if (temp _t'10 (Vint (Int.repr (if nz penc (Zlength e) + nz pout (Zlength cps) =? 0 then 0 else 1)))).
{ forward. entailer!. nz_cases. }
{ forward_if (temp _t'10 (Vint (Int.repr (if nz penc (Zlength e) + nz pout (Zlength cps) =? 0 then 0 else 1)))).
  { eapply derives_trans; [ | apply (mblock_tc (tarray tuint (Zlength cps)) pout TT) ]; [ cancel | simpl; rep_lia ]. }
  { forward. forward. entailer!. rewrite nz_null by rep_lia. nz_cases. }
  { forward. entailer!. rewrite (nz_nonnull pout) by auto. nz_cases. } }
forward_if.
{ thaw FR. forward. Exists (Int.repr 0). entailer!. }
assert (Hz: nz penc (Zlength e) = 0 /\ nz pout (Zlength cps) = 0).
{ destruct (nz_01 penc (Zlength e)) as [E1 | E1]; rewrite E1 in *;
  destruct (nz_01 pout (Zlength cps)) as [E2 | E2]; rewrite E2 in *; simpl in *; auto;
  exfalso; apply Int.one_not_zero; assumption. }
destruct Hz as [Hz1 Hz2]. apply nz_0 in Hz1. apply nz_0 in Hz2.
thaw FR.
try unfold MORE_COMMANDS, abbreviate.
eapply semax_pre; [ | apply (piece_copy DE EC HIF Espec gv cps e pc plab vo ve penc pout) ].
unfold P_copy, main_frame, mblock. go_lower.
sep_apply (malloc_arr0_tuchar (Zlength e) penc ltac:(lia) Hz1).
sep_apply (malloc_arr0_tuint (Zlength cps) pout ltac:(lia) Hz2).
sep_apply (lab_split (Zlength cps) e plab ltac:(lia)).
entailer!.
Qed.
