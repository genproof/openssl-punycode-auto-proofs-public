(* The end of the piece stmt_mallocs (MainMallocs.v, MainMallocsB.v): the three checks after the decoder call.
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainLib OpensslPunycode.proof.harness.roundtrip.RtMainGlob.
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainMallocsA.

Local Open Scope logic.

(* The tail of stmt_mallocs after r = ossl_punycode_decode(...) (a verbatim sub-term of stmt_mallocs). *)
Definition stmt_checks : statement :=
(Ssequence
                                      (Scall None
                                        (Evar _gp_assert (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Ebinop Oeq (Etempvar _r tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) :: nil))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'23 (Evar _olen tuint))
                                          (Scall None
                                            (Evar _gp_assert (Tfunction
                                                               (tint :: nil)
                                                               tvoid
                                                               cc_default))
                                            ((Ebinop Oeq
                                               (Etempvar _t'23 tuint)
                                               (Etempvar _m tulong) tint) ::
                                             nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'12)
                                              (Evar _same_uints (Tfunction
                                                                  ((tptr tuint) ::
                                                                   (tptr tuint) ::
                                                                   tulong ::
                                                                   nil) tint
                                                                  cc_default))
                                              ((Etempvar _out (tptr tuint)) ::
                                               (Etempvar _cps (tptr tuint)) ::
                                               (Etempvar _m tulong) :: nil))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _t'12 tint) :: nil)))
                                          stmt_if))).

(* After the decoder call: r = 1, out = cps, olen = m. *)
Definition P_checks (gv: globals) (cps e: list Z) (pc plab vo ve penc pout: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1]
  (LOCALx [temp _r (Vint (Int.repr 1)); temp _out pout; temp _enc penc; temp _lab plab;
           temp _ulen (Vlong (Int64.repr (ulen_of cps)));
           temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (arr0 Ews tuint (Zlength cps) (vb cps) pout ::
         arr0 Ews tuchar (Zlength e) (vb e) (offset_val 4 plab) :: lab_rest (Zlength cps) (Zlength e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo :: data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

Lemma piece_checks : piece_if_stmt ->
  forall (Espec: OracleKind) gv cps e pc plab vo ve penc pout,
    semax Delta_main (P_checks gv cps e pc plab vo ve penc pout) stmt_checks main_ret.
Proof.
intros HIF. intros.
unfold P_checks, stmt_checks, main_frame, main_ret, main_post. abbreviate_semax.
Intros.
assert (He0 := Zlength_nonneg e). assert (Hm0 := Zlength_nonneg cps).
forward_call (Int.repr 1).
forward.
forward_call (Int.repr 1).
{ entailer!. rewrite Int64.eq_true. reflexivity. }
rewrite (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength cps) _ pout).
rewrite (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength cps) _ pc).
forward_call (Ews, pout, cps, Ews, pc, cps).
{ split; eapply Forall_impl; try exact H0; intros c Hc; simpl in Hc; rep_lia. }
destruct (list_eq_dec Z.eq_dec cps cps) as [_ | NE]; [ | contradiction NE; reflexivity ].
forward_call (Int.repr 1).
try unfold MORE_COMMANDS, abbreviate.
eapply semax_pre; [ | apply (HIF Espec gv cps e pc plab vo ve) ].
rewrite <- (arr0_tuint_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength cps) _ pc).
unfold P_if, main_frame. go_lower. sep_apply (lab_join (Zlength cps) e plab ltac:(lia)). entailer!.
Qed.
