(* pr_a2ulabel: the search of the end of the current label (the first '.' at or after st, or n). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.proof.harness.ARDefs.
Local Open Scope logic.

Section Piece.
Context {Espec: OracleKind}.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val) (st: Z) (k: sink) (cv: list val).

Lemma find_piece: forall R,
  ar_ctx shs ps s shk cap init shb shc ->
  it_ok s cap st k cv ->
  semax Delta_a2u (find_pre shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) s_find
    (overridePost (find_post shs ps s shk pk buf cap init shb shc pc v_sep v_nul v_d v_u st k cv) R).
Proof.
  intros R Hctx Hit. destruct R. unfold find_pre, find_post. abbreviate_semax.
  destruct Hctx as (Hrs & Hwk & Hwb & Hwc & Hbs & Hls & Hcap & Hli & Hps).
  destruct Hit as (Hst & Hk & Hcv & Ha).
  pose proof (lab_end_range s st Hst) as Hle.
  unfold s_find.
  forward_loop (EX e: Z,
  PROP (st <= e <= lab_end s st)
  LOCAL (temp _e (Vlong (Int64.repr e)); temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc))
  break: (PROP ()
  LOCAL (temp _e (Vlong (Int64.repr (lab_end s st))); temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc)).
  { Exists st. entailer!. }
  Intros e.
  forward_if (PROP () LOCAL (temp _t'1 (Val.of_bool ((e <? Zlength s) && negb (Znth e s =? 46))); temp _e (Vlong (Int64.repr e)); temp _st (Vlong (Int64.repr st)); temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc; lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep) SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d; data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep; arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk; sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc)).
  { unfold arr0. destruct (Z.eq_dec (Zlength s) 0) as [Z0|NZ]; [lia|].
    assert (Hb: 0 <= Znth e s <= Byte.max_unsigned).
    { unfold bytes_ok in Hbs. rewrite Forall_Znth in Hbs. apply Hbs. lia. }
    forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold vb at 1. rewrite Znth_map by lia.
    forward.
    entailer!.
    - destruct (Z.ltb_spec e (Zlength s)); [|lia]. simpl.
      destruct (zeq (Znth e s) 46) as [E|E]; [rewrite E; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity.
    - unfold arr0. destruct (Z.eq_dec (Zlength s) 0); [lia|]. cancel. }
  { forward. entailer!. destruct (Z.ltb_spec e (Zlength s)); [lia|]. reflexivity. }
  assert (Hrl: Zlength (rem s st) = Zlength s - st) by (unfold rem; rewrite Zlength_sublist by lia; lia).
  assert (Hrz: e < Zlength s -> Znth (e - st) (rem s st) = Znth e s) by (intro; unfold rem; rewrite Znth_sublist by lia; f_equal; lia).
  forward_if.
  { forward. Exists (e + 1). entailer!.
    destruct (Z.ltb_spec e (Zlength s)); [|discriminate].
    destruct (Z.eqb_spec (Znth e s) 46); [discriminate|].
    assert (e - st < dot_index (rem s st)).
    { apply dot_index_step; [unfold lab_end in H; lia|lia|rewrite Hrz by lia; auto]. }
    unfold lab_end in *. lia. }
  { forward. entailer!.
    assert (e = lab_end s st); [|subst; auto].
    destruct (Z.ltb_spec e (Zlength s)); [|lia].
    destruct (Z.eqb_spec (Znth e s) 46); [|discriminate].
    destruct (Z.eq_dec e (lab_end s st)); auto.
    exfalso. apply (dot_index_before (rem s st) (e - st)); [unfold lab_end in *; lia|rewrite Hrz by lia; auto]. }
Qed.

End Piece.
