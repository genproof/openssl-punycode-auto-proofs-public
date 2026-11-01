Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.shim.code.

(* Helper facts for the shim bodies: the signed-char view of strings, index_of, tolower, ncasecmp. *)

Local Open Scope logic.

Definition sv (b: Z) : val := Vint (Int.repr (sbyte b)).

Lemma str_ok_bytes: forall s, str_ok s -> bytes_ok (s ++ [0]).
Proof.
  intros s H. unfold bytes_ok. apply Forall_app. split.
  - eapply Forall_impl; [ | exact H]. intros b Hb. simpl in *. rep_lia.
  - repeat constructor; rep_lia.
Qed.

Lemma cstr_tschar: forall sh s p, str_ok s ->
  cstr sh s p = data_at sh (tarray tschar (Zlength s + 1)) (map sv (s ++ [0])) p.
Proof. intros. unfold cstr. apply data_at_tuchar_tschar. apply str_ok_bytes; auto. Qed.

Lemma Znth_sv_lt: forall s i, 0 <= i < Zlength s -> Znth i (map sv (s ++ [0])) = sv (Znth i s).
Proof. intros. rewrite Znth_map by (rewrite Zlength_app; simpl; list_solve). rewrite app_Znth1 by lia. auto. Qed.

Lemma Znth_sv_end: forall s, Znth (Zlength s) (map sv (s ++ [0])) = sv 0.
Proof. intros. rewrite Znth_map by (rewrite Zlength_app; simpl; list_solve). rewrite app_Znth2 by lia.
  rewrite Z.sub_diag. reflexivity. Qed.

Lemma Znth_s0_lt: forall s i, 0 <= i < Zlength s -> Znth i (s ++ [0]) = Znth i s.
Proof. intros. rewrite app_Znth1 by lia. auto. Qed.

Lemma Znth_s0_end: forall s, Znth (Zlength s) (s ++ [0]) = 0.
Proof. intros. rewrite app_Znth2 by lia. rewrite Z.sub_diag. reflexivity. Qed.

Lemma str_ok_Znth: forall s i, str_ok s -> 0 <= i < Zlength s -> 1 <= Znth i s <= 255.
Proof. intros. unfold str_ok in H. rewrite Forall_Znth in H. apply H. auto. Qed.

Lemma str0_Znth: forall s i, str_ok s -> 0 <= i <= Zlength s -> 0 <= Znth i (s ++ [0]) <= 255.
Proof. intros. pose proof (str_ok_bytes s H). unfold bytes_ok in H1. rewrite Forall_Znth in H1.
  apply H1. rewrite Zlength_app. simpl. list_solve. Qed.

Lemma sbyte_range: forall b, 0 <= b <= 255 -> -128 <= sbyte b <= 127.
Proof. intros. unfold sbyte. destruct (b <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. Qed.

Lemma sbyte_inj: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 -> sbyte a = sbyte b -> a = b.
Proof. intros. unfold sbyte in *.
  destruct (a <? 128) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
  destruct (b <? 128) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2 | apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia. Qed.

Lemma sbyte_repr_inj: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
  Int.repr (sbyte a) = Int.repr (sbyte b) -> a = b.
Proof. intros. pose proof (sbyte_range _ H). pose proof (sbyte_range _ H0).
  apply repr_inj_signed in H1; [ | unfold repable_signed; rep_lia..]. apply sbyte_inj; auto. Qed.

Lemma fc_len: forall n p, 0 <= n -> field_compatible (Tarray tschar n noattr) [] p ->
  n <= Ptrofs.max_unsigned /\ isptr p.
Proof. intros n p Hn H. destruct H as (Hp & _ & Hs & _). destruct p; try contradiction. simpl in Hs.
  rewrite Z.max_r in Hs by lia. pose proof (Ptrofs.unsigned_range i). split; auto; rep_lia. Qed.

Lemma xor32: forall c, 65 <= c <= 90 -> Int.xor (Int.repr c) (Int.repr 32) = Int.repr (c + 32).
Proof.
  intros. replace c with (65 + Z.of_nat (Z.to_nat (c - 65))) by lia.
  assert (Hk: (Z.to_nat (c - 65) < 26)%nat) by lia. revert Hk. generalize (Z.to_nat (c - 65)). intros k Hk.
  do 26 (destruct k as [|k]; [reflexivity | ]). lia.
Qed.

Lemma index_of_range: forall c s, 0 <= index_of c s <= Zlength s.
Proof. induction s; simpl. list_solve. destruct (a =? c); list_solve. Qed.

Lemma index_of_step: forall c s i, 0 <= i < Zlength s -> i <= index_of c s ->
  (Znth i s = c -> index_of c s = i) /\ (Znth i s <> c -> i + 1 <= index_of c s).
Proof.
  intros c s. induction s as [|x s IH]; intros i Hi Hle.
  - list_solve.
  - simpl in Hle |- *. destruct (x =? c) eqn:E.
    + apply Z.eqb_eq in E. assert (i = 0) by lia. subst. rewrite Znth_0_cons. split; auto. intros; lia.
    + apply Z.eqb_neq in E. destruct (Z.eq_dec i 0).
      * subst. rewrite Znth_0_cons. pose proof (index_of_range c s). split; intros; lia.
      * rewrite Znth_pos_cons by lia. rewrite Zlength_cons in Hi.
        destruct (IH (i - 1) ltac:(lia) ltac:(lia)). split; intros; [rewrite H by auto | specialize (H0 H1)]; lia.
Qed.

Lemma sign_ext_sbyte: forall c, 0 <= c <= 255 -> Int.sign_ext 8 (Int.repr c) = Int.repr (sbyte c).
Proof.
  intros.
  assert (E: Byte.unsigned (Byte.repr c) = c) by (rewrite Byte.unsigned_repr; rep_lia).
  assert (S: Byte.signed (Byte.repr c) = sbyte c).
  { unfold Byte.signed. rewrite E. unfold sbyte. change Byte.half_modulus with 128. change Byte.modulus with 256.
    destruct (c <? 128) eqn:E1; [ apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1 ];
      (destruct (zlt c 128); [ reflexivity || lia | reflexivity || lia ]). }
  rewrite <- E at 1. rewrite <- S. apply sbyte_ubyte_convert. rewrite E.
  apply Int.same_bits_eq. intros. rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8); auto. rewrite !Int.testbit_repr by auto.
  symmetry. apply Z.bits_above_log2; try lia.
  destruct (Z.eq_dec c 0). subst. simpl. lia.
  assert (Z.log2 c < 8). { apply Z.log2_lt_pow2; simpl; lia. } lia.
Qed.

Lemma tolower_range: forall x, -128 <= x <= 127 -> -128 <= tolower x <= 127.
Proof. intros. unfold tolower. destruct (65 <=? x) eqn:E1; destruct (x <=? 90) eqn:E2; simpl;
  try apply Z.leb_le in E1; try apply Z.leb_le in E2; try apply Z.leb_gt in E1; try apply Z.leb_gt in E2; lia. Qed.

Lemma tolower_zero: forall b, 0 <= b <= 255 -> tolower (sbyte b) = 0 -> b = 0.
Proof. intros. pose proof (sbyte_range b H). unfold tolower in H0.
  destruct (65 <=? sbyte b) eqn:E1; destruct (sbyte b <=? 90) eqn:E2; simpl in H0;
  try apply Z.leb_le in E1; try apply Z.leb_le in E2; try apply Z.leb_gt in E1; try apply Z.leb_gt in E2; try lia;
  unfold sbyte in *; destruct (b <? 128) eqn:E; try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma ncasecmp_step: forall l1 l2 i k, 0 <= i < Zlength l1 -> 0 <= i < Zlength l2 ->
  ncasecmp (sublist i (Zlength l1) l1) (sublist i (Zlength l2) l2) (S k) =
  (let t := tolower (sbyte (Znth i l1)) - tolower (sbyte (Znth i l2)) in
   if negb (t =? 0) then t else if Znth i l1 =? 0 then 0
   else ncasecmp (sublist (i + 1) (Zlength l1) l1) (sublist (i + 1) (Zlength l2) l2) k).
Proof. intros. rewrite (sublist_next i (Zlength l1)) by lia. rewrite (sublist_next i (Zlength l2)) by lia.
  reflexivity. Qed.

