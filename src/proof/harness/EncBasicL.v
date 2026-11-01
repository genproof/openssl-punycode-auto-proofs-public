(* pr_encode: facts about the prefix of the encoding (the failures before the main loop), the state of the
   copy loop of the basic code points, small entailment lemmas. *)
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


(* The encoding starts with the basic code points. *)
Lemma encode_prefix_basics: forall cps e, encode cps = Some e ->
  exists s, e = filter (fun c => c <? 128) cps ++ s.
Proof.
  intros. unfold encode in H. apply enc_rounds_prefix in H. destruct H as [s ->].
  destruct (0 <? Zlength (filter (fun c => c <? 128) cps)).
  - exists ([45] ++ s). rewrite !app_assoc. auto.
  - eauto.
Qed.

Lemma encode_fits_basics: forall cps ocap j, 0 <= j <= Zlength cps ->
  ocap < Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) -> encode_fits cps ocap = false.
Proof.
  intros. apply (fits_false_pre cps ocap (filter (fun c => c <? 128) (sublist 0 j cps))); auto.
  intros. apply encode_prefix_basics in H1. destruct H1 as [s ->].
  rewrite (filter_prefix _ cps j) by lia. exists (filter (fun c => c <? 128) (sublist j (Zlength cps) cps) ++ s).
  rewrite app_assoc. auto.
Qed.

Lemma encode_fits_delim: forall cps ocap, 0 < Zlength (filter (fun c => c <? 128) cps) ->
  ocap <= Zlength (filter (fun c => c <? 128) cps) -> encode_fits cps ocap = false.
Proof.
  intros. apply (fits_false_pre cps ocap (filter (fun c => c <? 128) cps ++ [45])).
  - intros. unfold encode in H1. apply enc_rounds_prefix in H1. destruct H1 as [s ->].
    replace (0 <? Zlength (filter (fun c => c <? 128) cps)) with true by lia. eauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma arr0_data_at {cs: compspecs}: forall sh t n v p, n <> 0 -> arr0 sh t n v p |-- data_at sh (tarray t n) v p.
Proof. intros. rewrite arr0_ne by auto. auto. Qed.

Lemma data_at_arr0 {cs: compspecs}: forall sh t n v p, n <> 0 -> data_at sh (tarray t n) v p |-- arr0 sh t n v p.
Proof. intros. rewrite arr0_ne by auto. auto. Qed.

Lemma RA_normal_oP: forall Q R, RA_normal (overridePost Q R) = Q.
Proof. intros Q R; destruct R; reflexivity. Qed.

Lemma RA_normal_loop1: forall Inv R, RA_normal (loop1_ret_assert Inv R) = Inv.
Proof. intros Inv R; destruct R; reflexivity. Qed.

Lemma brk_enc {cs: compspecs}: forall Delta Q X F R,
  ENTAIL Delta, RA_break (overridePost Q (frame_ret_assert (function_body_ret_assert tint X) F)) |-- R.
Proof. intros. simpl. intro rho. apply andp_left2. normalize. Qed.

Lemma cont_enc {cs: compspecs}: forall Delta Q X F R,
  ENTAIL Delta, RA_continue (overridePost Q (frame_ret_assert (function_body_ret_assert tint X) F)) |-- R.
Proof. intros. simpl. intro rho. apply andp_left2. normalize. Qed.

Definition stmt_basicbody := (Ssequence
                    (Sset _t'11
                      (Ederef
                        (Ebinop Oadd (Etempvar _cps (tptr tuint))
                          (Etempvar _j tulong) (tptr tuint)) tuint))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'11 tuint)
                                   (Econst_int (Int.repr 128) tint) tint)
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _out tulong)
                                       (Etempvar _ocap tulong) tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Sset _t'12
                              (Ederef
                                (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                  (Etempvar _j tulong) (tptr tuint)) tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                                  (Etempvar _out tulong) (tptr tuchar))
                                tuchar)
                              (Ecast (Etempvar _t'12 tuint) tuchar)))
                          (Ssequence
                            (Sset _out
                              (Ebinop Oadd (Etempvar _out tulong)
                                (Econst_int (Int.repr 1) tint) tulong))
                            (Sset _b
                              (Ebinop Oadd (Etempvar _b tulong)
                                (Econst_int (Int.repr 1) tint) tulong)))))
                      Sskip)).


(* The state of the copy loop before code point j (the temp j holds jv). *)
Definition basic_st (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (ocap: Z) (oinit: list val)
  (shl: share) (pl: val) (j jv: Z) : environ -> mpred :=
  PROP (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) <= ocap)
  LOCAL (temp _j (Vlong (Int64.repr jv));
         temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _out (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar ocap (bufv (filter (fun c => c <? 128) (sublist 0 j cps)) ocap oinit) po;
       data_at_ shl tulong pl).

