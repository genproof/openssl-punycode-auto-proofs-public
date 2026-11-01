(* Piece 8 of the main of harness/rt_roundtrip.c: count = m, r = ossl_punycode_decode(encoding, len, out, &count)
   and the two checks (TrtMainDefs), from the round trip of the model. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* ossl_punycode_decode's specification is stated under the unit's compspecs. *)
#[local] Instance CCE_ps : change_composite_env PS.CS CS := CCE_any _ _.
#[local] Instance CCE_ps' : change_composite_env CS PS.CS := CCE_any _ _.

(* The largest code point stays in the range of the code points. *)
Lemma trt8_largest_range: forall cps,
  Forall (fun x => 0 <= x <= Int.max_unsigned) cps -> 0 <= largest cps <= Int.max_unsigned.
Proof.
  intros cps H. unfold largest.
  assert (G: forall acc, 0 <= acc <= Int.max_unsigned -> 0 <= fold_left Z.max cps acc <= Int.max_unsigned).
  { induction H as [ | x l Hx Hl IH]; intros acc Ha; simpl; [ lia | apply IH; lia ]. }
  apply G. rep_lia.
Qed.

(* A largest code point above 127 needs at least one code point (the harness divides by m then). *)
Lemma trt8_nonempty: forall cps, 127 < largest cps -> 0 < Zlength cps.
Proof.
  intros [ | x l] H; [ compute in H; discriminate | ].
  rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

(* The value of the harness's test past largest <= 127, in 64-bit unsigned arithmetic: exactly the test in Z. *)
Lemma trt8_test_val: forall L m, 127 < L <= Int.max_unsigned -> 0 < m <= Int.max_unsigned ->
  Vint (Int.repr (if orb (L <=? 127) (L - 127 <=? 2 ^ 32 / m) then 1 else 0)) =
  bool2val (Int64.cmpu Cle (Int64.repr (L - 127))
              (Int64.divu (Int64.shl (Int64.repr 1) (Int64.repr 32)) (Int64.repr m))).
Proof.
  intros L m HL Hm.
  change (Int64.shl (Int64.repr 1) (Int64.repr 32)) with (Int64.repr (2 ^ 32)).
  assert (0 <= 2 ^ 32 / m <= 2 ^ 32)
    by (split; [ apply Z.div_pos; lia | apply Z.div_le_upper_bound; [ lia | ];
           rewrite <- (Z.mul_1_l (2 ^ 32)) at 1; apply Z.mul_le_mono_nonneg_r; lia ]).
  unfold Int64.divu. rewrite !Int64.unsigned_repr by rep_lia.
  unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (Z.leb_spec L 127); [ lia | ]. rewrite Bool.orb_false_l.
  set (q := 2 ^ 32 / m) in *. clearbody q.
  destruct (zlt q (L - 127)); destruct (Z.leb_spec (L - 127) q); reflexivity || lia.
Qed.

(* The harness's test, largest <= 127 or largest - 127 <= 2^32 / m in integer division, implies the bound of the
   model's round trip, (largest - 127) * m <= 2^32. *)
Lemma trt8_test_bound: forall L m, 0 < m -> 127 < L -> L - 127 <= 2 ^ 32 / m -> (L - 127) * m <= 2 ^ 32.
Proof.
  intros L m Hm HL H.
  pose proof (Z.mul_div_le (2 ^ 32) m Hm).
  apply Z.le_trans with (m * (2 ^ 32 / m))%Z; [ | lia ].
  rewrite Z.mul_comm. apply Z.mul_le_mono_nonneg_l; lia.
Qed.

(* Beyond the bound of the round trip the harness's test is false: the first check is skipped. *)
Lemma trt8_test_false: forall L m, 0 <= m -> 2 ^ 32 < (L - 127) * m ->
  orb (L <=? 127) (L - 127 <=? 2 ^ 32 / m) = false.
Proof.
  intros L m Hm H.
  assert (127 < L) by (destruct (Z.le_gt_cases L 127); [ nia | lia ]).
  assert (0 < m) by (destruct (Z.eq_dec m 0); [ subst; lia | lia ]).
  destruct (Z.leb_spec L 127); [ lia | ]. destruct (Z.leb_spec (L - 127) (2 ^ 32 / m)); [ | reflexivity ].
  pose proof (trt8_test_bound L m ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* The octets of an encoding are octets (ossl_punycode_decode's precondition). *)
Lemma trt8_bytes_ok: forall cps e,
  Forall (fun x => 0 <= x <= Int.max_unsigned) cps -> encode cps = Some e -> bytes_ok e.
Proof.
  intros cps e Hc He. pose proof (OpensslPunycode.proof.model.Roundtrip.encode_chars cps e Hc He) as Hch.
  unfold bytes_ok. rewrite Forall_forall in *. intros x Hx. specialize (Hch x Hx).
  rep_lia || (destruct Hch as [-> | [? | [? | [? Hin]]]]; try rep_lia;
    specialize (Hc x Hin); rep_lia).
Qed.

(* The outcome of ossl_punycode_decode on the encoding with capacity m = |cps|: the code points back with count = m,
   or (only beyond the bound of the round trip) a failure with count = m. *)
Lemma trt8_result: trt_model_stmt -> forall cps outs e,
  Forall (fun x => 0 <= x <= Int.max_unsigned) cps -> Zlength outs = Zlength cps ->
  encode cps = Some e -> Zlength e < Int.max_unsigned ->
  PS.decode_result e (Zlength cps) (vb outs) = (1, vb cps, Zlength cps) \/
  (exists a, PS.decode_result e (Zlength cps) (vb outs) = (0, a, Zlength cps) /\
     2 ^ 32 < (largest cps - 127) * Zlength cps).
Proof.
  intros HM cps outs e Hc Ho He Hl.
  assert (Hc': Forall (fun c => 0 <= c <= maxint) cps)
    by (eapply Forall_impl; [ | exact Hc ]; intros a Ha; unfold maxint; rep_lia).
  destruct (HM cps e Hc' He) as [Hle [Hok Hb]].
  unfold PS.decode_result. destruct (Z.leb_spec Int.max_unsigned (Zlength e)); [ lia | ].
  destruct (decode e (Zlength cps)) as [ok out] eqn:D. simpl in Hok.
  destruct ok.
  - left. rewrite (Hok eq_refl). rewrite sublist_nil'. rewrite app_nil_r. reflexivity. lia.
  - right. eexists. split; [ reflexivity | ].
    destruct (Z.le_gt_cases ((largest cps - 127) * Zlength cps) (2 ^ 32)) as [B | B]; [ | lia ].
    specialize (Hb B). discriminate.
Qed.

Lemma piece8 : trt_model_stmt -> piece8_stmt.
Proof.
  intros HM Espec gv vl vc cps outs e pc po pe. unfold pre8, T8, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  assert (Hc': Forall (fun c => 0 <= c <= maxint) cps)
    by (eapply Forall_impl; [ | eassumption ]; intros a Ha; unfold maxint; rep_lia).
  destruct (HM cps e Hc' H3) as [Hle _].
  pose proof (trt8_largest_range cps H1) as HL.
  pose proof (trt8_bytes_ok cps e H1 H3) as Hbytes.
  forward.
  forward.
  rewrite (arr0_tuint_cs CS PS.CS _ _ _ po). rewrite (arr0_tuchar_cs CS PS.CS _ _ _ pe).
  forward_call (gv, Ews, pe, e, Ews, po, Zlength cps, vb outs, Tsh, vc).
  { rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. cancel. }
  { rewrite Zlength_vb. lia. }
  forward.
  forward_if (temp _t'13 (Vint (Int.repr (if orb (largest cps <=? 127)
                                               (largest cps - 127 <=? 2 ^ 32 / Zlength cps) then 1 else 0)))).
  { forward. entailer!.
    rewrite !Int64.unsigned_repr in H5 by rep_lia. destruct (Z.leb_spec (largest cps) 127); [ reflexivity | lia ]. }
  { assert (127 < largest cps) by (rewrite !Int64.unsigned_repr in H5 by rep_lia; lia).
    pose proof (trt8_nonempty cps H6).
    forward.
    { entailer!. match goal with Hz: Int64.repr (Zlength cps) = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia;
        change (Int64.unsigned Int64.zero) with 0 in Hz end. lia. }
    entailer!. apply trt8_test_val; rep_lia. }
  destruct (trt8_result HM cps outs e H1 H H3 H4) as [Hres | [a [Hres Hbig]]];
    rewrite Hres; simpl fst; simpl snd.
  - forward_if True.
    { forward_call (Int.one). entailer!. }
    { forward. entailer!. }
    Intros.
    forward_if (temp _t'14 (Vint Int.one)).
    { forward.
      forward_if (temp _t'14 (Vint Int.one)).
      { rewrite (arr0_tuint_cs PS.CS HelperSpec.CS _ _ _ po), (arr0_tuint_cs CS HelperSpec.CS _ _ _ pc).
        rewrite <- seq_assoc.
        forward_call (Ews, po, cps, Ews, pc, cps).
        destruct (list_eq_dec Z.eq_dec cps cps) as [_ | E]; [ | contradiction E; reflexivity ].
        rewrite (arr0_tuint_cs HelperSpec.CS CS _ _ _ po), (arr0_tuint_cs HelperSpec.CS CS _ _ _ pc).
        forward. forward. entailer!. }
      { rewrite Int.unsigned_repr in * by rep_lia. contradiction. }
      entailer!. }
    { contradiction. }
    forward_call (Int.one).
    forward. Exists (Int.repr 0). entailer!.
  - rewrite (trt8_test_false (largest cps) (Zlength cps) (Zlength_nonneg _) Hbig).
    forward_if True.
    { contradiction. }
    { forward. entailer!. }
    Intros.
    forward_if (temp _t'14 (Vint Int.one)).
    { discriminate. }
    { forward_if (temp _t'14 (Vint Int.one)).
      { forward. forward. forward. entailer!. }
      { contradiction. } }
    forward_call (Int.one).
    forward. Exists (Int.repr 0). entailer!.
Qed.
