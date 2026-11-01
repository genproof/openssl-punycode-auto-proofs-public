(* VST facts used by the body of ossl_a2ulabel: the compspecs of the callees' units, the string pieces. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.

Local Open Scope logic.

Definition PkCS : compspecs := OpensslPunycode.proof.packet.PacketSpec.CS.
Definition ShCS : compspecs := OpensslPunycode.proof.shim.ShimSpec.CS.

#[export] Instance CCkp : change_composite_env PkCS CS. make_cs_preserve PkCS CS. Defined.
#[export] Instance CCpk : change_composite_env CS PkCS. make_cs_preserve CS PkCS. Defined.

Lemma pkt_to_packet: forall sh p,
  @data_at_ CS sh (Tstruct _wpacket_st noattr) p = @data_at_ PkCS sh OpensslPunycode.proof.packet.PacketSpec.t_pkt p.
Proof.
  intros. apply (f_equal (fun f => f p)). symmetry. apply (@data_at__change_composite PkCS CS CCkp). reflexivity.
Qed.

Lemma pkt_from_packet: forall sh v p,
  @data_at PkCS sh OpensslPunycode.proof.packet.PacketSpec.t_pkt v p |-- @data_at_ CS sh (Tstruct _wpacket_st noattr) p.
Proof.
  intros. rewrite pkt_to_packet. apply data_at_data_at_.
Qed.

(* The composites of the shim and packet units are among those of the punycode unit (with the same sizes): a type
   is no larger under their compspecs. *)
Lemma sizeof_composite: forall (cs: compspecs) i a,
  (@sizeof cs (Tstruct i a) = match Maps.PTree.get i (@cenv_cs cs) with Some co => co_sizeof co | None => 0 end) /\
  (@sizeof cs (Tunion i a) = match Maps.PTree.get i (@cenv_cs cs) with Some co => co_sizeof co | None => 0 end).
Proof. split; reflexivity. Qed.

Lemma cenv_in_puny_sh: forall id co,
  Maps.PTree.get id (@cenv_cs ShCS) = Some co ->
  exists co', Maps.PTree.get id (@cenv_cs CS) = Some co' /\ co_sizeof co' = co_sizeof co.
Proof.
  intros id co H. apply Maps.PTree.elements_correct in H.
  vm_compute in H. repeat (destruct H as [H|H]; [inv H; eexists; split; [vm_compute; reflexivity | reflexivity]|]).
  destruct H.
Qed.

Lemma cenv_in_puny_pk: forall id co,
  Maps.PTree.get id (@cenv_cs PkCS) = Some co ->
  exists co', Maps.PTree.get id (@cenv_cs CS) = Some co' /\ co_sizeof co' = co_sizeof co.
Proof.
  intros id co H. apply Maps.PTree.elements_correct in H.
  vm_compute in H. repeat (destruct H as [H|H]; [inv H; eexists; split; [vm_compute; reflexivity | reflexivity]|]).
  destruct H.
Qed.

Lemma sizeof_le_gen: forall cs0: compspecs,
  (forall id co, Maps.PTree.get id (@cenv_cs cs0) = Some co ->
     exists co', Maps.PTree.get id (@cenv_cs CS) = Some co' /\ co_sizeof co' = co_sizeof co) ->
  forall t, @sizeof cs0 t <= @sizeof CS t.
Proof.
  intros cs0 INC.
  induction t; try (simpl; lia).
  - simpl. pose proof (@Ctypes.sizeof_pos (@cenv_cs cs0) t).
    apply Z.mul_le_mono_nonneg_r; [lia | exact IHt].
  - rewrite (proj1 (sizeof_composite _ i a)), (proj1 (sizeof_composite CS i a)).
    destruct (Maps.PTree.get i (@cenv_cs cs0)) eqn:E.
    + destruct (INC _ _ E) as [co' [E' S]]. rewrite E', S. lia.
    + destruct (Maps.PTree.get i (@cenv_cs CS)); [pose proof (co_sizeof_pos c) | ]; lia.
  - rewrite (proj2 (sizeof_composite _ i a)), (proj2 (sizeof_composite CS i a)).
    destruct (Maps.PTree.get i (@cenv_cs cs0)) eqn:E.
    + destruct (INC _ _ E) as [co' [E' S]]. rewrite E', S. lia.
    + destruct (Maps.PTree.get i (@cenv_cs CS)); [pose proof (co_sizeof_pos c) | ]; lia.
Qed.

Lemma sizeof_sh_le: forall t, @sizeof ShCS t <= @sizeof CS t.
Proof. apply sizeof_le_gen. apply cenv_in_puny_sh. Qed.
Lemma sizeof_pk_le: forall t, @sizeof PkCS t <= @sizeof CS t.
Proof. apply sizeof_le_gen. apply cenv_in_puny_pk. Qed.

(* ---------------------------------------------------------------------- *)
(* Pieces of an octet array                                               *)
(* ---------------------------------------------------------------------- *)

Lemma fc_sub: forall N p0 a n,
  field_compatible (tarray tuchar N) [] p0 -> 0 <= a -> 0 <= n -> a + n <= N ->
  field_compatible (tarray tuchar n) [] (offset_val a p0).
Proof.
  intros N p0 a n FC Ha Hn Han.
  destruct p0; try (destruct FC; contradiction).
  destruct FC as [_ [_ [SZ [_ _]]]]. unfold size_compatible in SZ. simpl sizeof in SZ.
  split; [simpl; auto|]. split; [reflexivity|]. split; [|split; [|simpl; auto]].
  - unfold size_compatible. simpl offset_val. simpl sizeof.
    destruct (Z.eq_dec n 0).
    + subst. pose proof (Ptrofs.unsigned_range (Ptrofs.add i (Ptrofs.repr a))). lia.
    + rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr a) by rep_lia.
      rewrite Ptrofs.unsigned_repr by rep_lia. rep_lia.
  - simpl offset_val. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
Qed.

(* The octets a .. b - 1 of the list L in the array at p0. *)
Definition piece (sh: share) (L: list Z) (a b: Z) (p0: val) : mpred :=
  data_at sh (tarray tuchar (b - a)) (vb (sublist a b L)) (offset_val a p0).

Lemma piece_split: forall sh L N p0 a b c,
  field_compatible (tarray tuchar N) [] p0 -> Zlength L = N -> 0 <= a <= b -> b <= c <= N ->
  piece sh L a c p0 = piece sh L a b p0 * piece sh L b c p0.
Proof.
  intros sh L N p0 a b c FC HL Hab Hbc. unfold piece.
  pose proof (fc_sub N p0 a (c - a) FC ltac:(lia) ltac:(lia) ltac:(lia)) as FC2.
  rewrite (split2_data_at_Tarray_tuchar sh (c - a) (b - a)) by (rewrite ?Zlength_vb, ?Zlength_sublist; lia).
  rewrite field_address0_offset.
  2: { eapply field_compatible0_cons_Tarray; [reflexivity | exact FC2 | lia]. }
  rewrite offset_offset_val. simpl nested_field_offset.
  unfold vb. rewrite !sublist_map, !sublist_sublist by lia.
  replace (a + (0 + 1 * (b - a))) with b by lia.
  replace (0 + a) with a by lia. replace (b - a + a) with b by lia. replace (c - a + a) with c by lia.
  replace (c - a - (b - a)) with (c - b) by lia. reflexivity.
Qed.

Lemma piece_empty: forall sh L a p0, isptr (offset_val a p0) -> piece sh L a a p0 = emp.
Proof.
  intros. unfold piece. rewrite Z.sub_diag, sublist_nil. apply data_at_zero_array_eq; auto.
Qed.

(* A string of the code: the suffix of s from st, with its NUL. *)
Lemma cstr_piece: forall sh s pin st,
  0 <= st <= Zlength s -> isptr pin ->
  cstr sh (sublist st (Zlength s) s) (offset_val st pin) = piece sh (s ++ [0]) st (Zlength s + 1) pin.
Proof.
  intros. unfold cstr, piece. rewrite Zlength_sublist by lia.
  replace (Zlength s - st + 1) with (Zlength s + 1 - st) by lia.
  rewrite (sublist_app' st (Zlength s + 1) s [0]) by (rewrite ?Zlength_cons, ?Zlength_nil; lia).
  replace (Zlength s + 1 - Zlength s) with 1 by lia.
  rewrite (sublist_same 0 1 [0]) by reflexivity.
  apply (data_at_tuchar_cs ShCS CS).
Qed.

(* The literal "xn--" as a string of the shim. *)
Lemma xn_lit_cstr: forall gv,
  xn_lit gv = cstr Ers [120; 110; 45; 45] (gv ___stringlit_punycode_1).
Proof.
  intros. unfold xn_lit, cstr. rewrite (data_at_tuchar_cs ShCS CS).
  rewrite data_at_tuchar_tschar by (repeat constructor; rep_lia).
  reflexivity.
Qed.

(* An array that may be empty. *)
Lemma data_at_arr0: forall {cs: compspecs} sh t n v p,
  complete_legal_cosu_type t = true -> isptr p -> (n = 0 -> v = []) ->
  data_at sh (tarray t n) v p = arr0 sh t n v p.
Proof.
  intros. unfold arr0. destruct (Z.eq_dec n 0); auto. subst. rewrite H1 by auto.
  apply data_at_zero_array_eq; auto.
Qed.
