(* The second half of the piece stmt_mallocs (MainMallocs.v): copy_bytes and the decoder call, after the NULL tests of
   enc and out (its three checks: MainMallocsC.v). *)
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
Require Import OpensslPunycode.proof.harness.roundtrip.RtMainMallocsA OpensslPunycode.proof.harness.roundtrip.RtMainMallocsC.

Local Open Scope logic.

(* The tail of stmt_mallocs after the NULL tests (a verbatim sub-term of stmt_mallocs). *)
Definition stmt_copy : statement :=
(Ssequence
                                (Ssequence
                                  (Sset _t'25 (Evar _elen tulong))
                                  (Scall None
                                    (Evar _copy_bytes (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                    ((Etempvar _enc (tptr tuchar)) ::
                                     (Ebinop Oadd
                                       (Etempvar _lab (tptr tuchar))
                                       (Econst_int (Int.repr 4) tint)
                                       (tptr tuchar)) ::
                                     (Etempvar _t'25 tulong) :: nil)))
                                (Ssequence
                                  (Sassign (Evar _olen tuint)
                                    (Ecast (Etempvar _m tulong) tuint))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'24 (Evar _elen tulong))
                                        (Scall (Some _t'11)
                                          (Evar _ossl_punycode_decode 
                                          (Tfunction
                                            ((tptr tschar) :: tulong ::
                                             (tptr tuint) :: (tptr tuint) ::
                                             nil) tint cc_default))
                                          ((Ecast
                                             (Etempvar _enc (tptr tuchar))
                                             (tptr tschar)) ::
                                           (Etempvar _t'24 tulong) ::
                                           (Etempvar _out (tptr tuint)) ::
                                           (Eaddrof (Evar _olen tuint)
                                             (tptr tuint)) :: nil)))
                                      (Sset _r (Etempvar _t'11 tint)))
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
                                          stmt_if)))))).

(* Before stmt_copy: enc and out allocated (arr0: nothing when the size is 0), the encoding inside lab split out. *)
Definition P_copy (gv: globals) (cps e: list Z) (pc plab vo ve penc pout: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1]
  (LOCALx [temp _out pout; temp _enc penc; temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps)));
           temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (arr0 Ews tuchar (Zlength e) (Zrepeat Vundef (Zlength e)) penc ::
         arr0 Ews tuint (Zlength cps) (Zrepeat Vundef (Zlength cps)) pout ::
         arr0 Ews tuchar (Zlength e) (vb e) (offset_val 4 plab) :: lab_rest (Zlength cps) (Zlength e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at_ Tsh tuint vo :: data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

Lemma piece_copy : decode_encode_stmt -> encode_chars_stmt -> piece_if_stmt ->
  forall (Espec: OracleKind) gv cps e pc plab vo ve penc pout,
    semax Delta_main (P_copy gv cps e pc plab vo ve penc pout) stmt_copy main_ret.
Proof.
intros DE EC HIF. intros.
unfold P_copy, stmt_copy, main_frame, main_ret, main_post. abbreviate_semax.
Intros.
assert (Hbe: bytes_ok e) by (eapply enc_bytes_ok; eauto).
assert (He0 := Zlength_nonneg e). assert (Hm0 := Zlength_nonneg cps).
assert (HD := enc_decode_result cps e (Zrepeat Vundef (Zlength cps)) DE ltac:(assumption) ltac:(assumption)
  ltac:(assumption) ltac:(assumption) ltac:(list_solve)).
rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength e) _ penc).
rewrite (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength e) _ (offset_val 4 plab)).
assert_PROP (isptr plab) as Pplab by (unfold lab_rest; entailer!).
forward.
forward_call (Ews, penc, Zrepeat Vundef (Zlength e), Ews, offset_val 4 plab, e).
{ list_solve. }
forward.
rewrite <- (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength e) _ penc).
rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
forward.
forward_call (gv, Ews, penc, e, Ews, pout, Zlength cps, Zrepeat Vundef (Zlength cps), Tsh, vo).
{ list_solve. }
rewrite HD. simpl fst; simpl snd.
forward.
eapply semax_pre; [ | apply (piece_checks HIF Espec gv cps e pc plab vo ve penc pout) ].
rewrite <- (arr0_tuchar_cs CS OpensslPunycode.proof.harness.RefRt.CS Ews (Zlength e) _ (offset_val 4 plab)).
unfold P_checks, main_frame. entailer!.
Unshelve. all: apply CCE_any.
Qed.
