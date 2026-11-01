(* pr_encode: the copy of the basic code points (one iteration of the first loop): the case c < 128. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Definition stmt_basiclt := (Ssequence
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
                                (Econst_int (Int.repr 1) tint) tulong))))).

Lemma enc_basic_lt: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (j c: Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap -> 0 <= j < Zlength cps ->
  0 <= c <= Int.max_unsigned -> c < 128 ->
  @Znth val Vundef j (vb cps) = Vint (Int.repr c) ->
  filter (fun c => c <? 128) (sublist 0 (j + 1) cps) = filter (fun c => c <? 128) (sublist 0 j cps) ++ [c] ->
  Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) <= ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _t'11 (Vint (Int.repr c)); temp _j (Vlong (Int64.repr j));
      temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
      temp _out (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
      temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
         arr0 sho tuchar ocap (bufv (filter (fun c => c <? 128) (sublist 0 j cps)) ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_basiclt
   (overridePost (basic_st shc pc cps sho po ocap oinit shl pl (j + 1) j)
      (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros until c. intros SH SH0 SH1 H H0 H1 H2 H3 Hc Hlt Hv Hfs H4.
  assert (Hfail: ocap <= Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) -> encode_fits cps ocap = false).
  { intros. apply (encode_fits_basics cps _ (j + 1)); [lia |].
    rewrite Hfs, Zlength_app, Zlength_cons, Zlength_nil. lia. }
  unfold basic_st, stmt_basiclt, enc_post. rewrite Hfs.
  remember (filter (fun c => c <? 128) (sublist 0 j cps)) as bj eqn:Ebj. clear Ebj Hfs.
  pose proof (Zlength_nonneg bj) as Hbj.
  abbreviate_semax.
  forward_if.
  + forward. apply ret0_entail; [ | apply bufv_len; lia ].
    fix_cmp. apply Hfail. lia.
  + fix_cmp.
    replace_SEP 0 (data_at shc (tarray tuint (Zlength cps)) (vb cps) pc); [entailer!; apply arr0_data_at; lia |].
    forward. { entailer!. rewrite Hv. simpl. auto. }
    rewrite Hv.
    replace_SEP 0 (arr0 shc tuint (Zlength cps) (vb cps) pc); [entailer!; apply data_at_arr0; lia |].
    replace_SEP 1 (data_at sho (tarray tuchar ocap) (bufv bj ocap oinit) po);
      [entailer!; apply arr0_data_at; lia |].
    forward.
    rewrite !(zext8 c) by lia. rewrite bufv_upd by lia.
    replace_SEP 1 (arr0 sho tuchar ocap (bufv (bj ++ [c]) ocap oinit) po);
      [entailer!; apply data_at_arr0; lia |].
    forward. forward.
    entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    repeat match goal with |- _ /\ _ => split end; try lia; f_equal; f_equal; lia.
Qed.
