(* The sub-packet record of a static WPACKET: the 40 zero octets of CRYPTO_zalloc (zblock, an array of unsigned char
   at Shim.CS) are a struct wpacket_sub with all fields zero (parent = NULL), and any struct wpacket_sub is again 40
   octets for CRYPTO_free. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

Lemma uchar0_zeros {cs: compspecs}: forall sh b z,
  readable_share sh -> Ptrofs.unsigned z + 1 < Ptrofs.modulus ->
  data_at sh tuchar (Vint Int.zero) (Vptr b z) |-- mapsto_zeros 1 sh (Vptr b z).
Proof.
  intros sh b z Hsh Hz.
  assert_PROP (field_compatible tuchar [] (Vptr b z)) as FC by entailer!.
  rewrite <- (mapsto_data_at' sh tuchar (Vint Int.zero)) by auto.
  unfold mapsto, mapsto_zeros. simpl access_mode. simpl type_is_volatile. cbv beta iota. rewrite if_true by auto.
  apply orp_left.
  - apply andp_right.
    + apply prop_right. pose proof (Ptrofs.unsigned_range z). lia.
    + simpl Z.to_nat. unfold mapsto_memory_block.address_mapsto_zeros. rewrite predicates_sl.sepcon_emp.
      apply andp_left2. apply derives_refl.
  - normalize. discriminate.
Qed.

Lemma arr_zeros {cs: compspecs}: forall sh, readable_share sh -> forall n, 0 <= n -> forall p,
  data_at sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) p |-- mapsto_zeros n sh p.
Proof.
  intros sh Hsh n Hn. pattern n; apply natlike_ind; [ | | exact Hn]; clear n Hn.
  - intros p. assert_PROP (field_compatible (tarray tuchar 0) [] p) as FC by entailer!.
    destruct p; try (destruct FC as [FC _]; contradiction).
    unfold mapsto_zeros. apply andp_right.
    + apply prop_right. destruct FC as [_ [_ [SZ _]]]. simpl in SZ. pose proof (Ptrofs.unsigned_range i). lia.
    + simpl. apply data_at_tuchar_zero_array_inv.
  - intros n Hn IH p.
    assert_PROP (field_compatible (tarray tuchar (Z.succ n)) [] p) as FC by entailer!.
    replace (Zrepeat (Vint Int.zero) (Z.succ n)) with ([Vint Int.zero] ++ Zrepeat (Vint Int.zero) n)
      by (unfold Zrepeat; rewrite Z2Nat.inj_succ by lia; reflexivity).
    rewrite (split2_data_at_Tarray_app 1) by (rewrite ?Zlength_Zrepeat; try reflexivity; lia).
    rewrite (data_at_singleton_array_eq sh tuchar (Vint Int.zero)) by reflexivity.
    rewrite field_address0_offset by auto with field_compatible.
    replace (Z.succ n - 1) with n by lia.
    destruct p; try (destruct FC as [FC _]; contradiction).
    destruct FC as [_ [_ [SZ _]]]. simpl in SZ. rewrite Z.max_r in SZ by lia.
    pose proof (Ptrofs.unsigned_range i).
    pose proof (aggregate_pred.mapsto_zeros_split sh b (Ptrofs.unsigned i) 1 n ltac:(lia) Hn ltac:(lia)) as SPL.
    rewrite Ptrofs.repr_unsigned in SPL. replace (Z.succ n) with (1 + n) by lia. rewrite SPL.
    apply sepcon_derives.
    + apply uchar0_zeros; auto. lia.
    + simpl offset_val.
      replace (Ptrofs.add i (Ptrofs.repr 1)) with (Ptrofs.repr (Ptrofs.unsigned i + 1)) by reflexivity.
      apply IH.
Qed.

(* The record as CRYPTO_zalloc returns it is a struct wpacket_sub with all fields zero. *)
Definition sub_zero : reptype t_sub :=
  (nullval, (Vlong Int64.zero, (Vlong Int64.zero, (Vlong Int64.zero, Vint Int.zero)))).

Lemma zero_val_sub: zero_val t_sub = sub_zero.
Proof.
  rewrite zero_val_eq. apply JMeq_eq. eapply JMeq_trans; [apply fold_reptype_JMeq |].
  simpl. unfold struct_zero_val. simpl. rewrite zero_val_tptr, zero_val_tulong, zero_val_tuint. apply JMeq_refl.
Qed.

Lemma zblock_to_sub: forall p, malloc_compatible sub_size p ->
  @data_at OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) (Zrepeat (Vint Int.zero) sub_size) p
  |-- data_at Ews t_sub sub_zero p.
Proof.
  intros p MC.
  rewrite (data_at_tuchar_cs _ CS).
  assert (FC: field_compatible t_sub [] p).
  { apply malloc_compatible_field_compatible; [exact MC | reflexivity | reflexivity]. }
  eapply derives_trans; [apply arr_zeros; auto; unfold sub_size; lia |].
  change sub_size with (sizeof t_sub).
  rewrite <- zero_val_sub.
  apply mapsto_zero_data_at_zero; [auto | reflexivity | reflexivity | exact FC].
Qed.

(* Any struct wpacket_sub is 40 octets (for CRYPTO_free). *)
Lemma sub_to_bytes: forall v p,
  data_at Ews t_sub v p |-- @data_at_ OpensslPunycode.proof.shim.ShimSpec.CS Ews (tarray tuchar sub_size) p.
Proof.
  intros v p.
  rewrite <- (data_at__tuchar_cs CS).
  eapply derives_trans; [apply data_at_data_at_ |].
  rewrite data_at__memory_block. Intros.
  rewrite <- memory_block_data_at_; [apply derives_refl |].
  destruct H as [? [? [? [? ?]]]].
  destruct p; try contradiction.
  split; [exact I |]. split; [reflexivity |]. split; [exact H1 |]. split; [| exact I].
  apply align_compatible_rec_Tarray. intros. econstructor; [reflexivity | apply Z.divide_1_l].
Qed.
