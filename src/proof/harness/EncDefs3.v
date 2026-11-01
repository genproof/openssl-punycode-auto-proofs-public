(* Shared definitions of the round pieces of pr_encode (EncMin.v, EncRound.v, BodyEncode.v): the invariant of the
   main loop, the Clight sub-statements of a round, the unfolding of enc_rounds. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Lemma enc_rounds_step: forall cps f n d bi h b out, h < Zlength cps ->
  enc_rounds cps (S f) n d bi h b out =
  if orb (maxint <? d) ((maxint - d) / (h + 1) <? min_ge cps n - n) then None
  else kont cps f (min_ge cps n) cps (d + (min_ge cps n - n) * (h + 1)) bi h b out.
Proof.
  intros. cbn [enc_rounds]. replace (Zlength cps <=? h) with false by lia. unfold kont. reflexivity.
Qed.

Lemma enc_rounds_done: forall cps f n d bi h b out, Zlength cps <= h ->
  enc_rounds cps (S f) n d bi h b out = Some out.
Proof. intros. cbn [enc_rounds]. replace (Zlength cps <=? h) with true by lia. reflexivity. Qed.

Lemma kont_nil: forall cps f n d bi h b out,
  kont cps f n [] d bi h b out = enc_rounds cps f (n + 1) (d + 1) bi h b out.
Proof. reflexivity. Qed.

(* The invariant of the main loop (while h < m): the rounds left after code point n - 1. *)
Definition enc_inv (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (ocap: Z) (oinit: list val)
  (shl: share) (pl: val) (B: Z) : environ -> mpred :=
  EX n: Z, EX delta: Z, EX bias: Z, EX h: Z, EX out: list Z, EX f: nat,
  PROP (encode cps = enc_rounds cps f n delta bias h B out; (Zlength cps - h < Z.of_nat f)%Z;
        h = cnt_lt n cps; 128 <= n <= maxint + 1; 0 <= delta <= maxint + 1; 0 <= bias <= 2400;
        Zlength out <= ocap)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
         temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
         temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
       data_at_ shl tulong pl).

Definition stmt_min := (Ssequence
                          (Sset _j
                            (Ecast (Econst_int (Int.repr 0) tint) tulong))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                             (Etempvar _m tulong) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'9
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _cps (tptr tuint))
                                        (Etempvar _j tulong) (tptr tuint))
                                      tuint))
                                  (Sifthenelse (Ebinop Oge
                                                 (Etempvar _t'9 tuint)
                                                 (Etempvar _n tulong) tint)
                                    (Ssequence
                                      (Sset _t'10
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _cps (tptr tuint))
                                            (Etempvar _j tulong)
                                            (tptr tuint)) tuint))
                                      (Sset _t'1
                                        (Ecast
                                          (Ebinop Olt (Etempvar _t'10 tuint)
                                            (Etempvar _mm tulong) tint)
                                          tbool)))
                                    (Sset _t'1
                                      (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'1 tint)
                                  (Ssequence
                                    (Sset _t'8
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _cps (tptr tuint))
                                          (Etempvar _j tulong) (tptr tuint))
                                        tuint))
                                    (Sset _mm
                                      (Ecast (Etempvar _t'8 tuint) tulong)))
                                  Sskip)))
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tulong)
                                (Econst_int (Int.repr 1) tint) tulong)))).

Definition stmt_passloop := (Ssequence
                                  (Sset _j
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _j tulong)
                                                     (Etempvar _m tulong)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      stmt_passbody)
                                    (Sset _j
                                      (Ebinop Oadd (Etempvar _j tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong)))).

Definition stmt_round2 := (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Ogt (Etempvar _delta tulong)
                                           (Econst_long (Int64.repr 4294967295) tulong)
                                           tint)
                              (Sset _t'2 (Econst_int (Int.repr 1) tint))
                              (Sset _t'2
                                (Ecast
                                  (Ebinop Ogt
                                    (Ebinop Osub (Etempvar _mm tulong)
                                      (Etempvar _n tulong) tulong)
                                    (Ebinop Odiv
                                      (Ebinop Osub
                                        (Econst_long (Int64.repr 4294967295) tulong)
                                        (Etempvar _delta tulong) tulong)
                                      (Ebinop Oadd
                                        (Ecast (Etempvar _h tulong) tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong) tulong) tint) tbool)))
                            (Sifthenelse (Etempvar _t'2 tint)
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                              Sskip))
                          (Ssequence
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
                                      (Econst_int (Int.repr 1) tint) tulong))))))).

Definition stmt_round := (Ssequence
                      (Sset _mm
                        (Ebinop Oadd
                          (Econst_long (Int64.repr 4294967295) tulong)
                          (Econst_int (Int.repr 1) tint) tulong))
                      (Ssequence
                        stmt_min
                        stmt_round2)).
