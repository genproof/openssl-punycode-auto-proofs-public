(* Piece 13 of the main of harness/rfc_unique.c: gp_assert(len1 == len2), literal = last_delimiter(input1, len1)
   and the loop over the octets, whose checks hold by the model fact in pre13 (RunMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.DecModel.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunMainDefs.
Local Open Scope logic.

(* A property of octets decided by a boolean holds of every octet once checked on 0..255. *)
Lemma run13_byte_check (f: Z -> bool) b :
  forallb f (map Z.of_nat (seq 0 256)) = true -> 0 <= b <= 255 -> f b = true.
Proof.
  intros Hf Hb. rewrite forallb_forall in Hf. apply Hf.
  replace b with (Z.of_nat (Z.to_nat b)) by lia. apply in_map. apply in_seq. lia.
Qed.

(* `c | 32` of an octet c is an octet. *)
Lemma run13_lor_range b : 0 <= b <= 255 -> 0 <= Z.lor b 32 <= 255.
Proof.
  intros Hb. pose proof (run13_byte_check (fun b => andb (0 <=? Z.lor b 32) (Z.lor b 32 <=? 255)) b
    ltac:(vm_compute; reflexivity) Hb) as X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1, X2. lia.
Qed.

(* The value C computes for `c | 32` of an octet c (in int), and for `(unsigned char) (c | 32)`. *)
Lemma run13_or b : 0 <= b <= 255 -> Int.or (Int.repr b) (Int.repr 32) = Int.repr (Z.lor b 32).
Proof. intros. unfold Int.or. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma run13_lower b : 0 <= b <= 255 -> Int.zero_ext 8 (Int.or (Int.repr b) (Int.repr 32)) = Int.repr (Z.lor b 32).
Proof.
  intros. rewrite run13_or by lia. apply zero_ext_inrange.
  pose proof (run13_lor_range b H). rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma piece13 : piece13_stmt.
Proof.
  intros Espec gv v1 v2 bs1 bs2 pi1 pi2. unfold pre13, T13, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. destruct H3 as [HL Hdiff].
  forward_call (Int.one).
  { entailer!. rewrite HL, Int64.eq_true. reflexivity. }
  rewrite (arr0_tuchar_cs CS C.CS _ _ _ pi1).
  forward_call (Ews, pi1, bs1).
  rewrite <- (arr0_tuchar_cs CS C.CS _ _ _ pi1).
  forward_for_simple_bound (Zlength bs1) (EX i: Z,
    PROP ()
    LOCAL (temp _literal (Vlong (Int64.repr (last_delim bs1)));
           temp _input2 pi2; temp _len2 (Vlong (Int64.repr (Zlength bs2)));
           temp _input1 pi1; temp _len1 (Vlong (Int64.repr (Zlength bs1)));
           gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
    SEP (arr0 Ews tuchar (Zlength bs1) (vb bs1) pi1; arr0 Ews tuchar (Zlength bs2) (vb bs2) pi2;
         data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; TT)).
  { entailer!. }
  { assert (B1: 0 <= Znth i bs1 <= 255) by (pose proof (proj1 (Forall_Znth bs1 _) H i ltac:(lia)) as X; simpl in X; rep_lia).
    assert (B2: 0 <= Znth i bs2 <= 255) by (pose proof (proj1 (Forall_Znth bs2 _) H0 i ltac:(lia)) as X; simpl in X; rep_lia).
    unfold arr0. rewrite !if_false by lia.
    forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold vb at 1 2. rewrite !Znth_map by lia.
    forward_if.
    { assert (Hne: Znth i bs1 <> Znth i bs2) by (intro E; rewrite E in H4; contradiction).
      destruct (Hdiff i ltac:(lia) Hne) as [Hlit [Hlow Heq]].
      pose proof (DecModel.last_delim_range bs1) as Hld.
      forward.
      { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      unfold vb at 1. rewrite Znth_map by lia.
      forward.
      rewrite run13_lower by lia.
      forward_if (temp _t'18 (Vint Int.one)).
      { forward. entailer!. }
      { assert (E0: last_delim bs1 = 0) by lia. rewrite E0. forward. entailer!. }
      forward_call (Int.one).
      forward_if (temp _t'19 (Vint Int.one)).
      { forward. entailer!. destruct (zlt 122 (Z.lor (Znth i bs1) 32)); [ lia | reflexivity ]. }
      { lia. }
      forward_if (temp _t'20 (Vint Int.one)).
      { forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        unfold vb at 1. rewrite Znth_map by lia.
        forward. rewrite run13_or by lia. rewrite Heq. entailer!. rewrite Int.eq_true. reflexivity. }
      { discriminate. }
      forward_call (Int.one).
      entailer!. unfold arr0. rewrite !if_false by lia. cancel. }
    { forward. entailer!. unfold arr0. rewrite !if_false by lia. cancel. } }
  forward. Exists (Int.repr 0). entailer!.
Qed.
