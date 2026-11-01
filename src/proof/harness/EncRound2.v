(* pr_encode: the end of a round, after the overflow test: delta += (mm - n) (h + 1), n = mm, the pass, delta++, n++. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncPass.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.proof.harness.EncLoop.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Definition stmt_round3 := (Ssequence
                            (Sset _delta
                              (Ebinop Oadd (Etempvar _delta tulong)
                                (Ebinop Omul
                                  (Ebinop Osub (Etempvar _mm tulong)
                                    (Etempvar _n tulong) tulong)
                                  (Ebinop Oadd
                                    (Ecast (Etempvar _h tulong) tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)
                                  tulong) tulong))
                            (Ssequence
                              (Sset _n (Etempvar _mm tulong))
                              (Ssequence
                                stmt_passloop
                                (Ssequence
                                  (Sset _delta
                                    (Ebinop Oadd (Etempvar _delta tulong)
                                      (Econst_int (Int.repr 1) tint) tulong))
                                  (Sset _n
                                    (Ebinop Oadd (Etempvar _n tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))))).

Lemma enc_round_rest: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (B n delta bias h: Z)
  (out: list Z) (f: nat) (mm: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap -> 0 <= B <= Int.max_unsigned ->
  encode cps = kont cps f mm cps (delta + (mm - n) * (h + 1)) bias h B out ->
  Zlength cps - h < Z.of_nat (S f) -> h = cnt_lt n cps -> 128 <= n <= maxint + 1 -> 0 <= delta <= maxint ->
  0 <= bias <= 2400 -> Zlength out <= ocap ->
  n <= mm <= maxint -> (forall c, In c cps -> n <= c -> mm <= c) -> 1 <= cnt_eq mm cps ->
  (mm - n) * (h + 1) <= maxint - delta -> 0 <= (mm - n) * (h + 1) ->
  semax DeltaE (PROP () LOCAL (temp _mm (Vlong (Int64.repr mm));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_round3
   (overridePost (enc_inv shc pc cps sho po ocap oinit shl pl B) (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros until mm. intros ? ? ? ? ? ? ? ? Hk Hf Hh Hn Hd Hb Ho Hmm Hmin Hce Hmul Hmul0.
  pose proof (cnt_lt_le n cps) as Hcl.
  pose proof (Zlength_nonneg out) as Hol.
  subst h. set (h := cnt_lt n cps) in *.
  unfold stmt_round3, enc_post. abbreviate_semax.
  forward. forward.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (enc_passloop shc pc cps sho po ocap oinit shl pl f mm h B
        (delta + (mm - n) * (h + 1)) bias out); auto; try lia ].
    entailer!. }
  Intros delta' bias' h' out'.
  pose proof (cnt_round n mm cps ltac:(lia) Hmin) as Hcr.
  rewrite Nat2Z.inj_succ in Hf.
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  forward. forward.
  unfold enc_inv. Exists (mm + 1) (delta' + 1) bias' h' out' f. entailer!.
Qed.
