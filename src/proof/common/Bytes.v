(* Shared vocabulary of the specifications: octet lists as values, arrays that may be empty (and then NULL).
  *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.

(* The values of a list of octets (or of code points) stored in an array of unsigned char / unsigned int. *)
Definition vb (l: list Z) : list val := map (fun b => Vint (Int.repr b)) l.

Definition bytes_ok (l: list Z) : Prop := Forall (fun b => 0 <= b <= Byte.max_unsigned) l.

(* An array of n elements of type t at p, nothing when n = 0 (then p may be NULL, or a pointer whose
   zero-size array the caller keeps in its frame). *)
Definition arr0 {cs: compspecs} (sh: share) (t: type) (n: Z) (v: list (reptype t)) (p: val) : mpred :=
  if Z.eq_dec n 0 then emp else data_at sh (tarray t n) v p.

(* The arrays of scalars do not depend on the compspecs. *)
Lemma data_at_tuint_cs: forall (cs1 cs2: compspecs) sh n (v: list val) p,
  @data_at cs1 sh (tarray tuint n) v p = @data_at cs2 sh (tarray tuint n) v p.
Proof.
  intros.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity].
Qed.

Lemma arr0_tuchar_cs: forall (cs1 cs2: compspecs) sh n v p,
  @arr0 cs1 sh tuchar n v p = @arr0 cs2 sh tuchar n v p.
Proof. intros. unfold arr0. destruct (Z.eq_dec n 0); auto. apply data_at_tuchar_cs. Qed.

Lemma arr0_tuint_cs: forall (cs1 cs2: compspecs) sh n v p,
  @arr0 cs1 sh tuint n v p = @arr0 cs2 sh tuint n v p.
Proof. intros. unfold arr0. destruct (Z.eq_dec n 0); auto. apply data_at_tuint_cs. Qed.

Lemma vb_app: forall l1 l2, vb (l1 ++ l2) = vb l1 ++ vb l2.
Proof. intros. unfold vb. apply map_app. Qed.

Lemma Zlength_vb: forall l, Zlength (vb l) = Zlength l.
Proof. intros. unfold vb. apply Zlength_map. Qed.

(* The signed-char view of an array of octets (the code under test reads its strings as char). *)
Definition sbyte (b: Z) : Z := if b <? 128 then b else b - 256.

Lemma data_at_tuchar_tschar {cs: compspecs}: forall sh n l p,
  bytes_ok l ->
  data_at sh (tarray tuchar n) (vb l) p = data_at sh (tarray tschar n) (map (fun b => Vint (Int.repr (sbyte b))) l) p.
Proof.
  intros sh n l p OK.
  assert (E1: vb l = map Vubyte (map Byte.repr l)).
  { unfold vb. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [ | exact OK].
    intros b Hb. simpl. unfold Vubyte. rewrite Byte.unsigned_repr by (simpl in Hb; rep_lia). reflexivity. }
  assert (E2: map (fun b => Vint (Int.repr (sbyte b))) l = map Vbyte (map Byte.repr l)).
  { rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [ | exact OK].
    intros b Hb. simpl. unfold Vbyte. f_equal. f_equal.
    unfold Byte.signed. rewrite Byte.unsigned_repr by (simpl in Hb; rep_lia).
    unfold sbyte. change Byte.half_modulus with 128. change Byte.modulus with 256.
    destruct (b <? 128) eqn:E; [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ];
      (destruct (zlt b 128); [ reflexivity || lia | reflexivity || lia ]). }
  rewrite E1, E2. symmetry. apply data_at_tarray_tschar_tuchar.
Qed.
