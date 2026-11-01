(* Shared definitions of the pass and round pieces of pr_encode (EncPass.v, EncRound.v, BodyEncode.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma cnt_eq_le: forall n l, cnt_eq n l <= Zlength l.
Proof.
  unfold cnt_eq. induction l; simpl. rewrite !Zlength_nil; lia.
  destruct (a =? n); rewrite ?Zlength_cons; lia.
Qed.

Lemma encode_fits_none: forall cps ocap, encode cps = None -> encode_fits cps ocap = false.
Proof. unfold encode_fits; intros. rewrite H. auto. Qed.

Ltac fix_cmp := fix_ltu; repeat match goal with
  | H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
      rewrite (Int64.unsigned_repr x) in H by (unfold maxint in *; rep_lia)
  end.

(* The state of the pass over the code points for code point n, before code point j (the temp j holds jv);
   f: the fuel of the rounds after this one, h0: h at the start of the pass, B: the number of basic code points. *)
Definition pass_st (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (ocap: Z) (oinit: list val)
  (shl: share) (pl: val) (f: nat) (n h0 B j jv: Z) : environ -> mpred :=
  EX delta: Z, EX bias: Z, EX h: Z, EX out: list Z,
  PROP (encode cps = kont cps f n (sublist j (Zlength cps) cps) delta bias h B out;
        (h = h0 + cnt_eq n (sublist 0 j cps))%Z; 0 <= delta <= maxint; 0 <= bias <= 2400; Zlength out <= ocap)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
         temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
         temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr jv));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
       data_at_ shl tulong pl).

Definition stmt_passbody := (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _cps (tptr tuint))
                                                (Etempvar _j tulong)
                                                (tptr tuint)) tuint))
                                          (Sset _c
                                            (Ecast (Etempvar _t'7 tuint)
                                              tulong)))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _c tulong)
                                                         (Etempvar _n tulong)
                                                         tint)
                                            (Ssequence
                                              (Sset _delta
                                                (Ebinop Oadd
                                                  (Etempvar _delta tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _delta tulong)
                                                             (Econst_long (Int64.repr 4294967295) tulong)
                                                             tint)
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                Sskip))
                                            Sskip)
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _c tulong)
                                                         (Etempvar _n tulong)
                                                         tint)
                                            stmt_digs
                                            Sskip))).
