(* Shared definitions of the pieces of the body of pr_encode (BodyEncode.v): the output buffer, the function's
   postcondition, the Clight sub-statements (verbatim from harness/roundtrip code), failure lemmas. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

(* The output buffer after the octets l: l then the rest of the initial values. *)
Definition bufv (l: list Z) (ocap: Z) (oinit: list val) : list val := vb l ++ sublist (Zlength l) ocap oinit.

Lemma bufv_upd: forall l x ocap oinit, Zlength l < ocap -> Zlength oinit = ocap ->
  upd_Znth (Zlength l) (bufv l ocap oinit) (Vint (Int.repr x)) = bufv (l ++ [x]) ocap oinit.
Proof. intros. unfold bufv, vb. list_solve. Qed.

Lemma bufv_len: forall l ocap oinit, Zlength l <= ocap -> Zlength oinit = ocap -> Zlength (bufv l ocap oinit) = ocap.
Proof. intros. unfold bufv, vb. list_solve. Qed.

Lemma modu_repr64: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.modu (Int64.repr a) (Int64.repr b) = Int64.repr (a mod b).
Proof. intros. unfold Int64.modu. rewrite !Int64.unsigned_repr by auto. auto. Qed.

Lemma ltu64_true: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = true -> a < b.
Proof. intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1 by auto. destruct (zlt a b); auto; discriminate. Qed.

Lemma ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = false -> b <= a.
Proof. intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1 by auto. destruct (zlt a b); auto; [discriminate | lia]. Qed.

Ltac fix_ltu := repeat match goal with
  | H: Int64.ltu (Int64.repr _) (Int64.repr _) = true |- _ =>
      apply ltu64_true in H; [ | unfold maxint in *; rep_lia | unfold maxint in *; rep_lia ]
  | H: Int64.ltu (Int64.repr _) (Int64.repr _) = false |- _ =>
      apply ltu64_false in H; [ | unfold maxint in *; rep_lia | unfold maxint in *; rep_lia ]
  end.

Definition enc_post (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (ocap: Z) (oinit: list val)
  (shl: share) (pl: val) : ret_assert :=
  frame_ret_assert
  (function_body_ret_assert tint
     (EX o' : list val,
      PROP (Zlength o' = ocap)
      RETURN (Vint (Int.repr (if encode_fits cps ocap then 1 else 0)))
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
      arr0 sho tuchar ocap (encode_out cps ocap oinit o') po;
      if encode_fits cps ocap
      then data_at shl tulong (Vlong (Int64.repr (encode_len cps))) pl
      else data_at_ shl tulong pl))%argsassert) (stackframe_of f_pr_encode).

Definition DeltaE : tycontext := func_tycontext f_pr_encode Vprog Gprog_encode nil.

Lemma encode_out_false: forall cps ocap oinit o', encode_fits cps ocap = false -> encode_out cps ocap oinit o' = o'.
Proof.
  unfold encode_fits, encode_out; intros. destruct (encode cps); auto. rewrite H; auto.
Qed.

Lemma fits_false_pre: forall cps ocap pre, (forall e, encode cps = Some e -> exists s, e = pre ++ s) ->
  ocap < Zlength pre -> encode_fits cps ocap = false.
Proof.
  intros. apply fits_false. intros. destruct (H e H1) as [s ->]. rewrite Zlength_app.
  pose proof (Zlength_nonneg s). lia.
Qed.

(* A failing step inside the c == n branch: the output so far out ++ wr is at least ocap long and the encoding,
   if any, continues it with D2 (at least one octet). *)
Lemma kont_dig_fail: forall cps f n rest d' b' h' b out wr D2 ocap,
  encode cps = kont cps f n rest d' b' h' b (out ++ wr ++ D2) -> 1 <= Zlength D2 ->
  ocap <= Zlength (out ++ wr) -> encode_fits cps ocap = false.
Proof.
  intros. apply (fits_false_pre cps ocap (out ++ wr ++ D2)).
  - intros. rewrite H in H2. eapply kont_prefix; eauto.
  - rewrite app_assoc, Zlength_app. lia.
Qed.

(* The return of 0: o' := the current buffer (the goal left by forward on "return 0"). *)
Lemma ret0_entail: forall cps ocap oinit shc pc sho po shl pl buf,
  encode_fits cps ocap = false -> Zlength buf = ocap ->
  arr0 shc tuint (Zlength cps) (vb cps) pc * arr0 sho tuchar ocap buf po * data_at_ shl tulong pl
  |-- EX a : list val,
      !! (Zlength a = ocap /\ Vint (Int.repr 0) = Vint (Int.repr (if encode_fits cps ocap then 1 else 0))) &&
      (arr0 shc tuint (Zlength cps) (vb cps) pc *
       (arr0 sho tuchar ocap (encode_out cps ocap oinit a) po *
        (if encode_fits cps ocap then data_at shl tulong (Vlong (Int64.repr (encode_len cps))) pl
         else data_at_ shl tulong pl))).
Proof.
  intros. Exists buf. rewrite encode_out_false by auto. rewrite H.
  entailer!.
Qed.

Definition stmt_digbody2 := (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'4)
                                                                  (Evar _pr_digit_char 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                  ((Ebinop Oadd
                                                                    (Etempvar _t tulong)
                                                                    (Ebinop Omod
                                                                    (Ebinop Osub
                                                                    (Etempvar _q tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    (Ebinop Osub
                                                                    (Econst_long (Int64.repr 36) tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong) ::
                                                                   nil))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _o (tptr tuchar))
                                                                    (Etempvar _out tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Etempvar _t'4 tuchar)))
                                                              (Ssequence
                                                                (Sset _out
                                                                  (Ebinop Oadd
                                                                    (Etempvar _out tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _q
                                                                    (Ebinop Odiv
                                                                    (Ebinop Osub
                                                                    (Etempvar _q tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    (Ebinop Osub
                                                                    (Econst_long (Int64.repr 36) tulong)
                                                                    (Etempvar _t tulong)
                                                                    tulong)
                                                                    tulong))
                                                                  (Sset _k
                                                                    (Ebinop Oadd
                                                                    (Etempvar _k tulong)
                                                                    (Econst_long (Int64.repr 36) tulong)
                                                                    tulong))))).

Definition stmt_digbody1 := (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'3)
                                                            (Evar _pr_threshold 
                                                            (Tfunction
                                                              (tulong ::
                                                               tulong :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Etempvar _k tulong) ::
                                                             (Etempvar _bias tulong) ::
                                                             nil))
                                                          (Sset _t
                                                            (Etempvar _t'3 tulong)))
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Olt
                                                              (Etempvar _q tulong)
                                                              (Etempvar _t tulong)
                                                              tint)
                                                            Sbreak
                                                            Sskip)
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oge
                                                                (Etempvar _out tulong)
                                                                (Etempvar _ocap tulong)
                                                                tint)
                                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                              Sskip)
                                                            stmt_digbody2))).

Definition stmt_digbody := Ssequence Sskip stmt_digbody1.

Definition stmt_digpost := (Ssequence
                                                    (Sifthenelse (Ebinop Oge
                                                                   (Etempvar _out tulong)
                                                                   (Etempvar _ocap tulong)
                                                                   tint)
                                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                      Sskip)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'5)
                                                          (Evar _pr_digit_char 
                                                          (Tfunction
                                                            (tulong :: nil)
                                                            tuchar
                                                            cc_default))
                                                          ((Etempvar _q tulong) ::
                                                           nil))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _o (tptr tuchar))
                                                              (Etempvar _out tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Etempvar _t'5 tuchar)))
                                                      (Ssequence
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
                                                                tulong))))))).

(* The branch c == n of the pass: q = delta; k = 36; the digit loop; the last digit, adapt, delta = 0, h++. *)
Definition stmt_digs :=
  Ssequence (Sset _q (Etempvar _delta tulong))
    (Ssequence (Sset _k (Econst_long (Int64.repr 36) tulong))
      (Ssequence (Sloop stmt_digbody Sskip) stmt_digpost)).

Section DigAsserts.
Variables (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (ocap: Z) (oinit: list val)
  (shl: share) (pl: val) (n delta bias h b j: Z) (out: list Z).

(* The invariant of the digit loop: wr written, q and k = 36 (65 - f2) for the remaining fuel f2. *)
Definition dig_inv : environ -> mpred :=
  EX q: Z, EX f2: nat, EX wr: list Z,
    PROP (enc_digits 64 delta 36 bias = wr ++ enc_digits f2 q (36 + 36 * (64 - Z.of_nat f2)) bias;
          0 <= q < 10 ^ Z.of_nat f2; q <= maxint; (f2 <= 64)%nat; Zlength (out ++ wr) <= ocap)
    LOCAL (temp _q (Vlong (Int64.repr q)); temp _k (Vlong (Int64.repr (36 + 36 * (64 - Z.of_nat f2))));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength (out ++ wr))));
      temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv (out ++ wr) ocap oinit) po;
         data_at_ shl tulong pl).

(* After the digit loop: the last digit q remains. *)
Definition dig_brk : environ -> mpred :=
  EX q: Z, EX wr: list Z,
    PROP (enc_digits 64 delta 36 bias = wr ++ [digit_char q]; 0 <= q < 26; Zlength (out ++ wr) <= ocap)
    LOCAL (temp _q (Vlong (Int64.repr q));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength (out ++ wr))));
      temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv (out ++ wr) ocap oinit) po;
         data_at_ shl tulong pl).

(* After the branch c == n. *)
Definition dig_q : environ -> mpred :=
  PROP (Zlength (out ++ enc_digits 64 delta 36 bias) <= ocap)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr 0));
    temp _bias (Vlong (Int64.repr (adapt delta (h + 1) (h =? b))));
    temp _out (Vlong (Int64.repr (Zlength (out ++ enc_digits 64 delta 36 bias))));
    temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr (h + 1))); temp _j (Vlong (Int64.repr j));
    temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
    temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar ocap (bufv (out ++ enc_digits 64 delta 36 bias) ocap oinit) po;
       data_at_ shl tulong pl).

End DigAsserts.

Lemma arr0_ne {cs: compspecs}: forall sh t n v p, n <> 0 -> arr0 sh t n v p = data_at sh (tarray t n) v p.
Proof. intros. unfold arr0. destruct (Z.eq_dec n 0); auto; lia. Qed.

Lemma zext8: forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Ltac repr0_false := match goal with C: Int64.repr _ = Int64.zero |- _ => apply (f_equal Int64.unsigned) in C;
  rewrite Int64.unsigned_repr in C by (unfold maxint in *; rep_lia); rewrite Int64.unsigned_zero in C; lia end.
