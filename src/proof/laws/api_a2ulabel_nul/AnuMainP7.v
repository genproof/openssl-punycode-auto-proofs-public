(* The second piece of the main of harness/api_a2ulabel_nul.c: from the call of ossl_a2ulabel to the end
   (AnuMainDefs): the call on the string of in (its octets up to the first NUL); when it returns 1, the search of
   the first NUL of out and the check that it is within outlen and that every octet after it is that of saved. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_a2ulabel_nul.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuMainDefs.
Local Open Scope logic.

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* The input array = the string (its octets up to the first NUL, with the NUL), then the rest. *)
Lemma in_split_first0 len bs pin:
  Zlength bs = len ->
  data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin =
  (OpensslPunycode.proof.shim.ShimSpec.cstr Ews (sublist 0 (first0 bs) bs) pin *
   data_at Ews (tarray tuchar (len - first0 bs)) (vb (sublist (first0 bs + 1) (len + 1) (bs ++ [0])))
     (field_address0 (tarray tuchar (len + 1)) (SUB (first0 bs + 1)) pin))%logic.
Proof.
  intros Hlen. pose proof (first0_range bs).
  unfold OpensslPunycode.proof.shim.ShimSpec.cstr.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.shim.ShimSpec.CS CS).
  rewrite (first0_split bs) at 1. unfold vb. rewrite map_app.
  rewrite (split2_data_at_Tarray_app (first0 bs + 1)).
  - replace (len + 1 - (first0 bs + 1)) with (len - first0 bs) by lia.
    replace (Zlength (sublist 0 (first0 bs) bs) + 1) with (first0 bs + 1) by list_solve. subst len. reflexivity.
  - list_solve.
  - list_solve.
Qed.

(* An array as bytes_eq's argument (nothing when it is empty). *)
Lemma data_at_arr0 (cs1 cs2: compspecs) sh n v q:
  @data_at cs1 sh (tarray tuchar n) v q |-- @arr0 cs2 sh tuchar n v q * TT.
Proof.
  unfold arr0. destruct (Z.eq_dec n 0); [ cancel | ].
  rewrite (data_at_tuchar_cs cs1 cs2). cancel.
Qed.

(* A loaded element shows as Znth at the reptype's Inhabitant instance: back to the val one. *)
Ltac fixZ := match goal with |- context [@Znth ?A ?d ?i ?l] => change (@Znth A d i l) with (Znth i l) end.

Lemma piece7 {Espec: OracleKind} gv len bs pin outlen pout psaved ob:
  semax Delta_main (pre7 gv len bs pin outlen pout psaved ob) (Ssequence T7 ret0) main_post.
Proof.
  intros. unfold pre7, T7, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  rewrite (in_split_first0 len bs pin) by auto. Intros.
  forward_call (gv, Ews, pin, sublist 0 (first0 bs) bs, Ews, pout, outlen, vb ob, tk0, 0, 0, 0).
  { split; [ apply first0_str; auto | split ].
    - right. rewrite Zlength_vb. auto.
    - unfold OpensslPunycode.proof.shim.ShimSpec.shim_bounds. rep_lia. }
  Intros mf.
  pose proof (a2u_outcome_res pout outlen (sublist 0 (first0 bs) bs) (vb ob) 0 0 mf) as Hres.
  pose proof (a2u_outcome_nul pout outlen (sublist 0 (first0 bs) bs) (vb ob) 0 0 mf ltac:(auto)
    (first0_str bs ltac:(auto)) ltac:(lia)) as Hnul.
  remember (OpensslPunycode.proof.punycode.PunySpec.a2u_outcome pout outlen (sublist 0 (first0 bs) bs) (vb ob) 0 0 mf)
    as oc.
  destruct oc as [[[r fn'] zf'] ov]. simpl in Hnul, Hres |- *. clear Heqoc.
  forward_if (PROP () LOCAL () SEP (TT)).
  2: { forward. entailer!. }
  2: { forward. Exists (Int.repr 0). entailer!. }
  (* r == 1: the octets written, then those of out after them *)
  assert (r = 1) as Hr1.
  { destruct Hres as [-> | [-> | ->]]; auto; match goal with H: Int.repr _ = Int.repr 1 |- _ =>
      apply repr_inj_signed in H; rep_lia end. }
  destruct (Hnul Hr1) as [w' [-> [Hw Hl]]]. clear Hnul Hres.
  set (m := Zlength w') in *.
  assert (0 <= m) by (subst m; apply Zlength_nonneg).
  unfold OpensslPunycode.proof.punycode.PunySpec.out_buf. rewrite if_false by auto. Intros.
  rewrite (data_at_tuchar_cs OpensslPunycode.proof.punycode.PunySpec.CS CS).
  set (OV := vb w' ++ Vint (Int.repr 0) :: sublist (m + 1) outlen (vb ob)).
  assert (HOV: Zlength OV = outlen) by (subst OV; rewrite Zlength_app, Zlength_cons, Zlength_sublist, Zlength_vb;
    rewrite ?Zlength_vb; lia).
  forward.
  forward_loop (EX e: Z,
    PROP (0 <= e <= m)
    LOCAL (temp _end (Vlong (Int64.repr e)); temp _saved psaved; temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)))
    SEP (data_at Ews (tarray tuchar outlen) OV pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))
  break: (PROP ()
    LOCAL (temp _end (Vlong (Int64.repr m)); temp _saved psaved; temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)))
    SEP (data_at Ews (tarray tuchar outlen) OV pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT)).
  { Exists 0. entailer!. }
  { Intros e.
    forward_if (PROP ()
      LOCAL (temp _t'9 (Vint (Int.repr (if Z.eq_dec e m then 0 else 1))); temp _end (Vlong (Int64.repr e));
             temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen)))
      SEP (data_at Ews (tarray tuchar outlen) OV pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT)).
    { assert (HZ: Znth e OV = Vint (Int.repr (if Z.eq_dec e m then 0 else Znth e w'))).
      { subst OV. destruct (Z.eq_dec e m) as [-> | N].
        - rewrite app_Znth2 by (rewrite Zlength_vb; lia). rewrite Zlength_vb, Z.sub_diag. reflexivity.
        - rewrite app_Znth1 by (rewrite Zlength_vb; lia). unfold vb. rewrite Znth_map by lia. reflexivity. }
      assert (HB: 0 <= (if Z.eq_dec e m then 0 else Znth e w') <= 255 /\
                  ((if Z.eq_dec e m then 0 else Znth e w') = 0 <-> e = m)).
      { destruct (Z.eq_dec e m) as [-> | N]; [ split; [ lia | tauto ] | ].
        assert (nz (Znth e w')) by (apply Forall_Znth; auto; lia). unfold nz in *. split; [ lia | ]. split; [ lia | tauto ]. }
      forward.
      { entailer!. fixZ. rewrite HZ. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      fixZ. rewrite HZ. forward.
      entailer!.
      destruct HB as [_ HB]. destruct (Z.eq_dec e m) as [E | E]; [ reflexivity | ].
      destruct (zeq (Znth e w') 0) as [E2 | E2]; [ exfalso; apply E, HB, E2 | reflexivity ]. }
    { exfalso; lia. }
    (* if (!t'9) break; end++ *)
    forward_if (PROP (e <> m)
      LOCAL (temp _end (Vlong (Int64.repr e)); temp _saved psaved; temp _out pout;
             temp _outlen (Vlong (Int64.repr outlen)))
      SEP (data_at Ews (tarray tuchar outlen) OV pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT)).
    { forward. destruct (Z.eq_dec e m) as [E | E]; entailer!. }
    { destruct (Z.eq_dec e m) as [E | E]; forward; [ rewrite E; entailer! | ].
      entailer!. match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. }
    Intros.
    forward. Exists (e + 1). entailer!. }
  (* gp_assert(end < outlen && bytes_eq(out + end + 1, saved + end + 1, outlen - end - 1)) *)
  forward_if (PROP () LOCAL (temp _t'10 (Vint Int.one)) SEP (TT)).
  { set (L := sublist (m + 1) outlen ob).
    assert (HL: Zlength L = outlen - (m + 1)) by (subst L; rewrite Zlength_sublist; lia).
    assert (E1: OV = vb (w' ++ [0]) ++ vb L) by (subst OV L; rewrite vb_app; unfold vb; rewrite <- sublist_map;
      rewrite <- app_assoc; reflexivity).
    assert (E2: vb ob = vb (sublist 0 (m + 1) ob) ++ vb L) by (subst L; rewrite <- vb_app, <- sublist_split,
      sublist_same; auto; lia).
    assert_PROP (field_compatible (tarray tuchar outlen) [] pout /\ field_compatible (tarray tuchar outlen) [] psaved)
      as FF by entailer!.
    destruct FF as [Fo Fs].
    assert (Ipo: isptr pout) by (destruct Fo; auto). assert (Ips: isptr psaved) by (destruct Fs; auto).
    rewrite E1, E2.
    rewrite (split2_data_at_Tarray_app (m + 1) outlen Ews tuchar (vb (w' ++ [0])) (vb L) pout)
      by (rewrite ?Zlength_vb, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
    rewrite (split2_data_at_Tarray_app (m + 1) outlen Ews tuchar (vb (sublist 0 (m + 1) ob)) (vb L) psaved)
      by (rewrite ?Zlength_vb, ?Zlength_sublist; lia).
    Intros.
    rewrite !field_address0_offset by auto with field_compatible.
    sep_apply (data_at_arr0 CS CCS Ews (outlen - (m + 1)) (vb L)
      (offset_val (nested_field_offset (tarray tuchar outlen) [ArraySubsc (m + 1)]) pout)).
    sep_apply (data_at_arr0 CS CCS Ews (outlen - (m + 1)) (vb L)
      (offset_val (nested_field_offset (tarray tuchar outlen) [ArraySubsc (m + 1)]) psaved)).
    Intros.
    rewrite <- HL.
    forward_call (Ews, offset_val (nested_field_offset (tarray tuchar outlen) [ArraySubsc (m + 1)]) pout, L,
                  Ews, offset_val (nested_field_offset (tarray tuchar outlen) [ArraySubsc (m + 1)]) psaved, L).
    { entailer!. destruct pout; try contradiction. destruct psaved; try contradiction. simpl. rewrite HL.
      replace (Zlength ob - m - 1) with (Zlength ob - (m + 1)) by lia.
      replace (0 + 1 * (m + 1)) with (m + 1) by lia. reflexivity. }
    { subst L; split; apply Forall_sublist; auto. }
    destruct (list_eq_dec Z.eq_dec L L) as [_ | C]; [ | contradiction ].
    forward. entailer!. }
  { exfalso; lia. }
  forward_call.
  entailer!.
Qed.
