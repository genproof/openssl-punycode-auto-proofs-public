(* pr_encode, the branch c == n of the pass: after the last digit is stored (adapt, delta = 0, h++). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Definition stmt_digpost2 := (Ssequence
                                                        (Sset _out
                                                          (Ebinop Oadd
                                                            (Etempvar _out tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'6)
                                                              (Evar _pr_adapt 
                                                              (Tfunction
                                                                (tulong ::
                                                                 tulong ::
                                                                 tint :: nil)
                                                                tulong
                                                                cc_default))
                                                              ((Etempvar _delta tulong) ::
                                                               (Ebinop Oadd
                                                                 (Ecast
                                                                   (Etempvar _h tulong)
                                                                   tulong)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tulong) ::
                                                               (Ebinop Oeq
                                                                 (Etempvar _h tulong)
                                                                 (Etempvar _b tulong)
                                                                 tint) ::
                                                               nil))
                                                            (Sset _bias
                                                              (Etempvar _t'6 tulong)))
                                                          (Ssequence
                                                            (Sset _delta
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tulong))
                                                            (Sset _h
                                                              (Ebinop Oadd
                                                                (Etempvar _h tulong)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tulong))))).

Lemma enc_dig_post2: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z) (q: Z) (wr: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Zlength out <= ocap ->
  enc_digits 64 delta 36 bias = wr ++ [digit_char q] -> 0 <= q < 26 -> Zlength (out ++ wr) < ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _t'5 (Vint (Int.repr (digit_char q))); temp _q (Vlong (Int64.repr q));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength (out ++ wr))));
      temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
         arr0 sho tuchar ocap (bufv ((out ++ wr) ++ [digit_char q]) ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_digpost2
   (normal_ret_assert (dig_q shc pc cps sho po ocap oinit shl pl n delta bias h b j out)).
Proof.
  intros until wr. intros ? ? ? ? ? ? H5 ? ? ? ? ? Hd Hq Hw.
  unfold dig_q, stmt_digpost2. abbreviate_semax.
  pose proof (Zlength_nonneg (out ++ wr)) as Hwl.
  forward.
  forward_call (delta, h + 1, if h =? b then 1 else 0).
  { entailer!. simpl. unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zeq h b), (h =? b) eqn:E; try reflexivity; [apply Z.eqb_neq in E | apply Z.eqb_eq in E]; lia. }
  { destruct (h =? b); rep_lia. }
  replace (negb ((if h =? b then 1 else 0) =? 0)) with (h =? b) by (destruct (h =? b); reflexivity).
  forward. forward.
  entailer!.
  { assert (E: Zlength ((out ++ wr) ++ [digit_char q]) = Zlength (out ++ wr) + 1)
      by (rewrite Zlength_app; reflexivity).
    rewrite Hd, app_assoc, E. split; [lia | reflexivity]. }
  rewrite Hd, app_assoc. auto.
Qed.
