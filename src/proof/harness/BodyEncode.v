(* The body of pr_encode (harness/puny_ref.h, RFC 3492 6.3), under the roundtrip harness's compspecs.
  *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.proof.harness.EncRound.
Require Import OpensslPunycode.proof.harness.EncBasicL.
Require Import OpensslPunycode.proof.harness.EncBasic.
Require Import OpensslPunycode.proof.harness.EncMain.
Local Open Scope logic.

Lemma RA_normal_for: forall I R, RA_normal (for_ret_assert I R) = I.
Proof. intros I R; destruct R; reflexivity. Qed.

Lemma body_pr_encode : semax_body Vprog Gprog_encode f_pr_encode pr_encode_spec.
Proof.
start_function.
forward. forward. forward. forward. forward.
forward_for_simple_bound (Zlength cps) (EX j: Z,
  PROP (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)) <= ocap)
  LOCAL (temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _out (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) (sublist 0 j cps)))));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar ocap (bufv (filter (fun c => c <? 128) (sublist 0 j cps)) ocap oinit) po;
       data_at_ shl tulong pl)).
{ entailer!.
  - rewrite sublist_nil. simpl. rewrite Zlength_nil. lia.
  - unfold bufv. rewrite sublist_nil. simpl filter. unfold vb; simpl map.
    rewrite Zlength_nil, sublist_same by lia. simpl app. auto. }
{ rename i into j.
  eapply semax_pre; [ | eapply semax_post; [ | | | | apply (enc_basic_body shc pc cps sho po ocap oinit shl pl j); auto ] ].
  { unfold basic_st. entailer!. }
  { rewrite RA_normal_oP. unfold POSTCONDITION, abbreviate. rewrite RA_normal_for. apply ENTAIL_refl. }
  { apply brk_enc. }
  { apply cont_enc. }
  { intros. apply ENTAIL_refl. } }
rewrite sublist_same by lia.
pose proof (Zlength_nonneg (filter (fun c => c <? 128) cps)) as HB0.
assert (HB1: Zlength (filter (fun c => c <? 128) cps) <= Zlength cps) by (unfold cnt_lt; apply (cnt_lt_le 128 cps)).
forward.
forward_if (PROP (Zlength (if 0 <? Zlength (filter (fun c => c <? 128) cps)
                           then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps) <= ocap)
  LOCAL (temp _out (Vlong (Int64.repr (Zlength (if 0 <? Zlength (filter (fun c => c <? 128) cps)
                           then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps))));
         temp _h (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) cps))));
         temp _b (Vlong (Int64.repr (Zlength (filter (fun c => c <? 128) cps))));
         temp _bias (Vlong (Int64.repr 72)); temp _delta (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar ocap (bufv (if 0 <? Zlength (filter (fun c => c <? 128) cps)
                           then filter (fun c => c <? 128) cps ++ [45] else filter (fun c => c <? 128) cps) ocap oinit) po;
       data_at_ shl tulong pl)).
{ fix_cmp. replace (0 <? Zlength (filter (fun c => c <? 128) cps)) with true by lia.
  forward_if.
  - forward. apply ret0_entail; [ | apply bufv_len; lia ].
    fix_cmp. apply encode_fits_delim; lia.
  - fix_cmp.
    replace_SEP 1 (data_at sho (tarray tuchar ocap) (bufv (filter (fun c => c <? 128) cps) ocap oinit) po);
      [entailer!; apply arr0_data_at; lia |].
    forward.
    rewrite !(zext8 45) by lia. rewrite bufv_upd by lia.
    replace_SEP 1 (arr0 sho tuchar ocap (bufv (filter (fun c => c <? 128) cps ++ [45]) ocap oinit) po);
      [entailer!; apply data_at_arr0; lia |].
    forward. entailer!.
    all: replace (0 <? Zlength (filter (fun c => c <? 128) cps)) with true by lia; auto.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    repeat match goal with |- _ /\ _ => split end; try lia; f_equal; f_equal; lia. }
{ fix_cmp. forward. entailer!.
  all: replace (0 <? Zlength (filter (fun c => c <? 128) cps)) with false by lia; auto. }
Intros.
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
eapply enc_main; auto.
Qed.
