(* Piece 7 of the main of harness/rfc_digit_case.c: literal = last_delimiter(input, len) and the loop that changes
   the case of letters of other's deltas (RdcMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcModel.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.

(* The facts of the loop: other starts as a copy of the input, and each change of a letter's case at a position of
   the deltas keeps it related to the input by case_rel. *)
Lemma case_rel_refl s bs: case_rel s bs bs.
Proof. split; [ reflexivity | split; reflexivity ]. Qed.

Lemma case_rel_upd s bs bs' i c:
  case_rel s bs bs' -> 0 <= s -> s <= i < Zlength bs -> lower c = lower (Znth i bs') -> case_rel s bs (upd_Znth i bs' c).
Proof.
  intros [HL [HP HC]] Hs Hi Hc. split; [ rewrite Zlength_upd_Znth; auto | split ].
  - intros j Hj Hjs. rewrite upd_Znth_diff by lia. auto.
  - intros j Hj. destruct (Z.eq_dec j i).
    + subst. rewrite upd_Znth_same by lia. rewrite Hc. auto.
    + rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma lower_sub32 c: 97 <= c <= 122 -> lower (c - 32) = lower c.
Proof.
  intros H. unfold lower.
  destruct (Z.leb_spec 65 (c - 32)), (Z.leb_spec (c - 32) 90), (Z.leb_spec 65 c), (Z.leb_spec c 90);
    simpl; lia.
Qed.

Lemma lower_add32 c: 65 <= c <= 90 -> lower (c + 32) = lower c.
Proof.
  intros H. unfold lower.
  destruct (Z.leb_spec 65 (c + 32)), (Z.leb_spec (c + 32) 90), (Z.leb_spec 65 c), (Z.leb_spec c 90);
    simpl; lia.
Qed.

Lemma delta_start_range bs: 0 <= delta_start bs <= Zlength bs.
Proof.
  unfold delta_start. pose proof (OpensslPunycode.proof.punycode.DecModel.last_delim_range bs) as [H0 H1].
  pose proof (Zlength_nonneg bs).
  destruct (Z.eqb_spec (last_delim bs) 0); lia.
Qed.

Lemma vb_upd i l c: 0 <= i < Zlength l -> upd_Znth i (vb l) (Vint (Int.repr c)) = vb (upd_Znth i l c).
Proof. intros. unfold vb. exact (upd_Znth_map (fun b => Vint (Int.repr b)) i l c). Qed.

Lemma bytes_ok_upd i l c: bytes_ok l -> 0 <= c <= Byte.max_unsigned -> bytes_ok (upd_Znth i l c).
Proof.
  intros H Hc. unfold bytes_ok in *. destruct (zlt i 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt i (Zlength l)); [ | rewrite upd_Znth_out_of_range by lia; auto ].
  apply Forall_upd_Znth; auto.
Qed.

Lemma arr0_pos {cs: compspecs} sh t n v p: 0 < n -> arr0 sh t n v p = data_at sh (tarray t n) v p.
Proof. intros. unfold arr0. rewrite if_false by lia. reflexivity. Qed.

Lemma piece7 : piece9_stmt -> piece7_stmt.
Proof.
  intros H9 Espec gv v1 v2 bs pi ps init1 po1 init2 po2. unfold pre7, T7, ret0, main_post, Delta_main.
  abbreviate_semax. Intros.
  rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi).
  forward_call (Ews, pi, bs).
  rewrite <- (arr0_tuchar_cs CS C.CS _ _ _ pi).
  pose proof (delta_start_range bs) as Hds.
  pose proof (OpensslPunycode.proof.punycode.DecModel.last_delim_range bs) as [Hl0 Hl1].
  forward_if (temp _t'11 (Vlong (Int64.repr (delta_start bs)))).
  { forward. entailer!. unfold delta_start.
    destruct (Z.eqb_spec (last_delim bs) 0).
    - rewrite e in H5. discriminate.
    - reflexivity. }
  { forward. entailer!. unfold delta_start.
    destruct (Z.eqb_spec (last_delim bs) 0); [ reflexivity | ].
    exfalso. destruct Hl1 as [E | E]; [ contradiction | ].
    rewrite Int64.unsigned_repr in H5 by lia. rewrite Int64.unsigned_repr in H5 by rep_lia. lia. }
  forward.
  forward_loop (EX i: Z, EX bs': list Z,
    PROP (delta_start bs <= i <= Zlength bs; case_rel (delta_start bs) bs bs'; bytes_ok bs')
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _out2 po2; temp _out1 po1;
           temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps; temp _input pi;
           temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
    SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength init1) (vb init1) po1;
         arr0 Ews tuint (Zlength init1) (vb init2) po2; arr0 Ews tuchar (Zlength bs) (vb bs') ps;
         data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; PS.puny_consts gv; mem_mgr gv; TT))
  continue: (EX i: Z, EX bs': list Z,
    PROP (delta_start bs <= i < Zlength bs; case_rel (delta_start bs) bs bs'; bytes_ok bs')
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _out2 po2; temp _out1 po1;
           temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps; temp _input pi;
           temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
    SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength init1) (vb init1) po1;
         arr0 Ews tuint (Zlength init1) (vb init2) po2; arr0 Ews tuchar (Zlength bs) (vb bs') ps;
         data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; PS.puny_consts gv; mem_mgr gv; TT))
  break: (EX bs': list Z,
    PROP (case_rel (delta_start bs) bs bs'; bytes_ok bs')
    LOCAL (temp _out2 po2; temp _out1 po1;
           temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps; temp _input pi;
           temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
    SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength init1) (vb init1) po1;
         arr0 Ews tuint (Zlength init1) (vb init2) po2; arr0 Ews tuchar (Zlength bs) (vb bs') ps;
         data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; PS.puny_consts gv; mem_mgr gv; TT)).
  { Exists (delta_start bs) bs. entailer!. apply case_rel_refl. }
  { Intros i bs'.
    forward_if.
    forward_call. Intros b.
    pose proof H6 as [HL [HP HC]].
    forward_if.
    { rewrite (arr0_pos Ews tuchar (Zlength bs) (vb bs') ps) by lia.
      assert (Hc: 0 <= Znth i bs' <= Byte.max_unsigned)
        by (unfold bytes_ok in H7; rewrite Forall_forall in H7; apply H7, Znth_In; lia).
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      unfold vb at 1; rewrite Znth_map by lia.
      forward_if (temp _t'13 (Vint (Int.repr (if andb (97 <=? Znth i bs') (Znth i bs' <=? 122) then 1 else 0)))).
      { forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        unfold vb at 1; rewrite Znth_map by lia.
        forward. entailer!.
        destruct (Z.leb_spec 97 (Znth i bs')), (Z.leb_spec (Znth i bs') 122), (zlt 122 (Znth i bs'));
          simpl; try reflexivity; lia. }
      { forward. entailer!. destruct (Z.leb_spec 97 (Znth i bs')); [ lia | reflexivity ]. }
      forward_if.
      { (* a lowercase letter: other[i] = other[i] - 32 *)
        forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        unfold vb at 1; rewrite Znth_map by lia.
        forward.
        assert (Hlo: 97 <= Znth i bs' <= 122)
          by (destruct (Z.leb_spec 97 (Znth i bs')), (Z.leb_spec (Znth i bs') 122); simpl in H12'; lia).
        assert (Hz: Int.zero_ext 8 (Int.sub (Int.repr (Znth i bs')) (Int.repr 32)) = Int.repr (Znth i bs' - 32)).
        { rewrite sub_repr. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. }
        rewrite Hz, (vb_upd i bs') by lia.
        Exists i (upd_Znth i bs' (Znth i bs' - 32)).
        rewrite (arr0_pos Ews tuchar (Zlength bs) (vb (upd_Znth i bs' (Znth i bs' - 32))) ps) by lia.
        entailer!.
        split; [ apply case_rel_upd; [ auto | lia | lia | apply lower_sub32; lia ]
               | apply bytes_ok_upd; [ auto | rep_lia ] ]. }
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      unfold vb at 1; rewrite Znth_map by lia.
      forward_if (temp _t'12 (Vint (Int.repr (if andb (65 <=? Znth i bs') (Znth i bs' <=? 90) then 1 else 0)))).
      { forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        unfold vb at 1; rewrite Znth_map by lia.
        forward. entailer!.
        destruct (Z.leb_spec 65 (Znth i bs')), (Z.leb_spec (Znth i bs') 90), (zlt 90 (Znth i bs'));
          simpl; try reflexivity; lia. }
      { forward. entailer!. destruct (Z.leb_spec 65 (Znth i bs')); [ lia | reflexivity ]. }
      forward_if.
      { (* an uppercase letter: other[i] = other[i] + 32 *)
        forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        unfold vb at 1; rewrite Znth_map by lia.
        forward.
        assert (Hup: 65 <= Znth i bs' <= 90)
          by (destruct (Z.leb_spec 65 (Znth i bs')), (Z.leb_spec (Znth i bs') 90); simpl in H13'; lia).
        assert (Hz: Int.zero_ext 8 (Int.add (Int.repr (Znth i bs')) (Int.repr 32)) = Int.repr (Znth i bs' + 32)).
        { rewrite add_repr. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. }
        rewrite Hz, (vb_upd i bs') by lia.
        Exists i (upd_Znth i bs' (Znth i bs' + 32)).
        rewrite (arr0_pos Ews tuchar (Zlength bs) (vb (upd_Znth i bs' (Znth i bs' + 32))) ps) by lia.
        entailer!.
        split; [ apply case_rel_upd; [ auto | lia | lia | apply lower_add32; lia ]
               | apply bytes_ok_upd; [ auto | rep_lia ] ]. }
      { (* not a letter *)
        forward. Exists i bs'. rewrite (arr0_pos Ews tuchar (Zlength bs) (vb bs') ps) by lia. entailer!. } }
    { forward. Exists i bs'. entailer!. }
    { forward. Exists bs'. entailer!. }
  }
  { Intros i bs'. forward. Exists (i + 1) bs'. entailer!. }
  Intros bs'.
  eapply semax_pre; [ | apply (H9 Espec gv v1 v2 bs bs' pi ps init1 po1 init2 po2) ].
  unfold pre9. entailer!.
Qed.
