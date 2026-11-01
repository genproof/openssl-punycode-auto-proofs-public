(* ossl_punycode_decode: the copy of the basic code points (if (basic_count > 0) {...}). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.DecInv.

Lemma basic_block: forall (Espec: OracleKind) gv shi pe inp sho pd cap (init: list val) shl pl,
  readable_share shi -> writable_share sho -> writable_share shl -> bytes_ok inp ->
  Zlength inp < Int.max_unsigned -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  semax (func_tycontext f_ossl_punycode_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _loop (Vint (Int.repr (Zlength inp)));
    temp _basic_count (Vint (Int.repr (last_delim inp)));
    temp _max_out (Vint (Int.repr cap)); temp _written_out (Vint (Int.repr 0));
    temp _processed_in (Vint (Int.repr 0)); temp _bias (Vint (Int.repr 72));
    temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
    temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
   SEP (puny_consts gv;
    arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap init pd;
    data_at shl tuint (Vint (Int.repr cap)) pl))
  stmt_basic
  (overridePost
   (PROP (Forall (fun c => c < 128) (sublist 0 (last_delim inp) inp); last_delim inp <= cap)
    LOCAL (temp _processed_in (Vint (Int.repr (if last_delim inp =? 0 then 0 else last_delim inp + 1)));
     temp _written_out (Vint (Int.repr (last_delim inp)));
     temp _max_out (Vint (Int.repr cap)); temp _bias (Vint (Int.repr 72));
     temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
     temp _enc_len (Vlong (Int64.repr (Zlength inp))); temp _pDecoded pd; temp _pout_length pl)
    SEP (puny_consts gv;
     arr0 shi tuchar (Zlength inp) (vb inp) pe;
     arr0 sho tuint cap (vb (sublist 0 (last_delim inp) inp) ++ sublist (last_delim inp) cap init) pd;
     data_at shl tuint (Vint (Int.repr cap)) pl))
   (dec_post gv shi pe inp sho pd cap init shl pl)).
Proof.
intros Espec gv shi pe inp sho pd cap init shl pl SH SH0 SH1 H LEN2 H1 H2.
unfold stmt_basic, dec_post. abbreviate_semax.
set (len := Zlength inp) in *.
assert (LEN: 0 <= len) by apply Zlength_nonneg.
pose proof (last_delim_range inp) as LD.
set (b := last_delim inp) in *.
forward_if.
{ rename H0 into BP.
  forward_if.
  { forward.
    rewrite (decode_result_eq _ _ _ false []) by (auto; apply decode_fail_cap; rep_lia).
    cbn [fst snd]. rewrite Zlength_nil, sublist_same by lia.
    change (vb []) with (@nil val). rewrite app_nil_l. entailer!. }
  assert (CAPP: cap <> 0) by lia.
  unfold arr0 at 2. rewrite if_false by auto.
  forward_for_simple_bound b (EX j: Z,
  PROP (Forall (fun c => c < 128) (sublist 0 j inp))
  LOCAL (temp _basic_count (Vint (Int.repr b));
    temp _max_out (Vint (Int.repr cap)); temp _written_out (Vint (Int.repr j));
    temp _processed_in (Vint (Int.repr 0)); temp _bias (Vint (Int.repr 72));
    temp _i (Vint (Int.repr 0)); temp _n (Vint (Int.repr 128)); gvars gv; temp _pEncoded pe;
    temp _enc_len (Vlong (Int64.repr len)); temp _pDecoded pd; temp _pout_length pl)
  SEP (puny_consts gv;
   arr0 shi tuchar len (vb inp) pe;
   data_at sho (tarray tuint cap) (vb (sublist 0 j inp) ++ sublist j cap init) pd;
   data_at shl tuint (Vint (Int.repr cap)) pl)).
  { entailer!. rewrite sublist_nil. change (vb []) with (@nil val). rewrite app_nil_l, sublist_same by lia. cancel. }
  { rewrite arr0_in by (auto; lia).
    pose proof (bytes_ok_Znth inp i H ltac:(lia)) as RB.
    pose proof (sbyte_range _ RB) as RS.
    forward.
    forward_call (Int.unsigned (Int.repr (sbyte (Znth i inp)))).
    { rewrite Int.repr_unsigned. entailer!. }
    rewrite is_basic_sbyte by auto.
    destruct (Znth i inp <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
    - forward_if. { lia. }
      forward. forward. forward.
      rewrite <- arr0_in by (auto; lia).
      entailer!.
      { apply Forall_sublist_snoc; auto; lia. }
      rewrite sbyte_small by lia. rewrite basic_store by lia. cancel.
    - forward_if.
      forward.
      rewrite (decode_result_eq _ _ _ false (sublist 0 i inp)) by (auto; apply decode_fail_basic; auto; lia).
      cbn [fst snd]. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
      unfold arr0. rewrite !if_false by lia. rewrite (data_at_tuchar_tschar _ _ inp) by auto.
      entailer!.
      lia. }
  forward.
  entailer!.
  { rewrite (proj2 (Z.eqb_neq b 0)) by lia. auto. }
  unfold arr0. rewrite if_false by lia. cancel. }
{ forward. assert (B0: b = 0) by lia. rewrite B0 in *.
  entailer!. rewrite sublist_nil. change (vb []) with (@nil val). rewrite app_nil_l, sublist_same by lia. cancel. }
Qed.
