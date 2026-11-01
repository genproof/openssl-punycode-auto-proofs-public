(* The globals of harness/rfc_samples.c as process_globals gives them (one block per initializer: the string
   literals as char arrays, encoded[] as 19 pointer cells, points[] and decoded[] as arrays of their
   initializers' integers, the constants of punycode.c as single cells), turned into the predicates of
   RsmMainDefs (lit, encoded_at, points_at, decoded_at) and of PunySpec.puny_consts.  The globals are processed in
   three chunks, RsmGlobA/B/C.v; the equations of the conversion lemmas are closed there by computation. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainLib.
Local Open Scope logic.

(* The literal of sample s, points[] and decoded[], as process_globals gives them: each part of the data_at a
   variable, equal to the expected one (by computation). *)
Lemma lit_conv gv s sh t (l: reptype t) q : 0 <= s < 19 ->
  sh = Ers -> t = tarray tschar (Zlength (enc s) + 1) -> JMeq l (vb (enc s ++ [0])) -> q = gv (Znth s lit_ids) ->
  data_at sh t l q = lit gv s.
Proof. intros Hs -> -> Hl ->. apply JMeq_eq in Hl. subst l. reflexivity. Qed.

Lemma points_conv gv sh t (l: reptype t) q :
  sh = Ers -> t = tarray tuchar 19 -> JMeq l (vb pts) -> q = gv _points -> data_at sh t l q = points_at gv.
Proof. intros -> -> Hl ->. apply JMeq_eq in Hl. subst l. reflexivity. Qed.

Lemma decoded_conv gv sh t (l: reptype t) q :
  sh = Ers -> t = tarray tuint 355 -> JMeq l (vb dec) -> q = gv _decoded -> data_at sh t l q = decoded_at gv.
Proof. intros -> -> Hl ->. apply JMeq_eq in Hl. subst l. reflexivity. Qed.

(* A constant of punycode.c (an unsigned int or the delimiter), as process_globals gives it. *)
Lemma tuint_conv (gv: globals) i sh t q v c : headptr (gv i) ->
  sh = Ers -> t = tuint -> q = gv i -> v = Vint (Int.repr c) ->
  mapsto sh t q v = data_at Ers tuint (Vint (Int.repr c)) (gv i).
Proof.
  intros Hi -> -> -> ->. rewrite (mapsto_data_at'' Ers tuint _ (Vint (Int.repr c))); auto.
Qed.

Lemma delim_conv (gv: globals) i sh t q v : headptr (gv i) ->
  sh = Ers -> t = tuchar -> q = gv i -> v = Vint (Int.zero_ext 8 (Int.repr 45)) ->
  mapsto sh t q v = data_at Ers tschar (Vint (Int.repr 45)) (gv i).
Proof.
  intros Hi -> -> -> ->. rewrite (mapsto_data_at'' Ers tuchar _ (Vint (Int.zero_ext 8 (Int.repr 45)))); auto.
  rewrite <- (data_at_singleton_array_eq Ers tuchar _ [Vint (Int.zero_ext 8 (Int.repr 45))] (gv i) eq_refl).
  rewrite <- (data_at_singleton_array_eq Ers tschar _ [Vint (Int.repr 45)] (gv i) eq_refl).
  change [Vint (Int.zero_ext 8 (Int.repr 45))] with (map Vubyte [Byte.repr 45]).
  change [Vint (Int.repr 45)] with (map Vbyte [Byte.repr 45]).
  rewrite data_at_tarray_tschar_tuchar. reflexivity.
Qed.

(* encoded[s] as a pointer cell. *)
Definition cell (gv: globals) (s: Z) : mpred :=
  data_at Ers (tptr tschar) (gv (Znth s lit_ids)) (offset_val (8 * s) (gv _encoded)).

Lemma encoded_fc (q: val) : headptr q -> field_compatible (tarray (tptr tschar) 19) [] q.
Proof.
  intros Hq. apply headptr_field_compatible; auto; [ reflexivity | simpl; rep_lia | ].
  apply align_compatible_rec_Tarray. intros i Hi. eapply align_compatible_rec_by_value; [ reflexivity | ].
  simpl. apply Z.divide_add_r; [ apply Z.divide_0_r | apply Z.divide_factor_l ].
Qed.

Lemma cell_fc (q: val) k : headptr q -> 0 <= k < 19 -> field_compatible (tptr tschar) [] (offset_val (8 * k) q).
Proof.
  intros Hq Hk. pose proof (encoded_fc q Hq) as F.
  pose proof (field_compatible_cons_Tarray k (tarray (tptr tschar) 19) (tptr tschar) 19 noattr [] q
    eq_refl F Hk) as F'.
  apply field_compatible_nested_field in F'. simpl in F'. rewrite Z.add_0_l in F'. exact F'.
Qed.

(* encoded[s] as process_globals gives it. *)
Lemma cell_conv gv s t a v : headptr (gv _encoded) -> isptr (gv (Znth s lit_ids)) -> 0 <= s < 19 ->
  t = tptr tschar -> a = offset_val (8 * s) (gv _encoded) -> v = offset_val 0 (gv (Znth s lit_ids)) ->
  mapsto Ers t a v = cell gv s.
Proof.
  intros He Hi Hs -> -> ->. unfold cell.
  rewrite (mapsto_data_at' Ers (tptr tschar) _ (gv (Znth s lit_ids)));
    [ reflexivity | reflexivity | reflexivity | | ].
  - apply cell_fc; auto.
  - destruct (gv (Znth s lit_ids)); try contradiction. simpl. rewrite Ptrofs.add_zero. apply JMeq_refl.
Qed.

Lemma cell_conv0 gv t a v : headptr (gv _encoded) -> isptr (gv (Znth 0 lit_ids)) ->
  t = tptr tschar -> a = gv _encoded -> v = offset_val 0 (gv (Znth 0 lit_ids)) ->
  mapsto Ers t a v = cell gv 0.
Proof.
  intros He Hi Ht Ha Hv. apply cell_conv; auto; [ lia | ].
  rewrite Ha. destruct He as [b ->]. simpl. rewrite Ptrofs.add_zero. reflexivity.
Qed.

(* The cells of encoded[] are its array. *)
Lemma cells_k gv k : (k <= 19)%nat -> headptr (gv _encoded) ->
  sep_list (cell gv) (map Z.of_nat (seq 0 k)) |--
  data_at Ers (tarray (tptr tschar) (Z.of_nat k)) (sublist 0 (Z.of_nat k) (map gv lit_ids)) (gv _encoded).
Proof.
  intros Hk He. pose proof Zlength_lit_ids as HL.
  assert (HL': Zlength (map gv lit_ids) = 19) by (rewrite Zlength_map; auto).
  induction k as [ | k IH].
  - simpl. rewrite sublist_nil. rewrite data_at_zero_array_eq; auto.
  - rewrite seq_S, map_app, sep_list_app. change (map Z.of_nat [(0 + k)%nat]) with [Z.of_nat k]. simpl (sep_list (cell gv) [_]). rewrite sepcon_emp.
    sep_apply IH; [ lia | ]. replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
    rewrite (sublist_split 0 (Z.of_nat k) (Z.of_nat k + 1)) by lia.
    rewrite (sublist_len_1 (Z.of_nat k)) by lia.
    rewrite (split2_data_at_Tarray_app (Z.of_nat k)); [ | change (@reptype CS (tptr tschar)) with val; list_solve | list_solve ].
    replace (Z.of_nat k + 1 - Z.of_nat k) with 1 by lia.
    rewrite (data_at_singleton_array_eq Ers (tptr tschar) (Znth (Z.of_nat k) (map gv lit_ids))) by reflexivity.
    rewrite Znth_map by lia. unfold cell. rewrite field_address0_offset.
    + simpl nested_field_offset. rewrite Z.add_0_l. cancel.
    + apply arr_field_compatible0; [ | lia ].
      apply field_compatible_array_smaller0 with 19; [ apply encoded_fc; auto | lia ].
Qed.

Lemma cells_encoded gv : headptr (gv _encoded) -> sep_list (cell gv) idx19 |-- encoded_at gv.
Proof.
  intros He. unfold encoded_at, idx19. sep_apply (cells_k gv 19 ltac:(lia) He). change (Z.of_nat 19) with 19.
  change (@reptype CS (tptr tschar)) with val.
  pose proof Zlength_lit_ids. rewrite sublist_same; [ apply derives_refl | lia | rewrite Zlength_map; lia ].
Qed.

(* The 19 literals and the 19 cells, one by one. *)
Lemma lits19 gv : lit gv 0 * lit gv 1 * lit gv 2 * lit gv 3 * lit gv 4 * lit gv 5 * lit gv 6 * lit gv 7 * lit gv 8 * lit gv 9 * lit gv 10 * lit gv 11 * lit gv 12 * lit gv 13 * lit gv 14 * lit gv 15 * lit gv 16 * lit gv 17 * lit gv 18 |-- lits gv.
Proof. unfold lits, idx19. simpl. rewrite !sepcon_emp. cancel. Qed.

Lemma cells19 gv : headptr (gv _encoded) ->
  cell gv 0 * cell gv 1 * cell gv 2 * cell gv 3 * cell gv 4 * cell gv 5 * cell gv 6 * cell gv 7 * cell gv 8 * cell gv 9 * cell gv 10 * cell gv 11 * cell gv 12 * cell gv 13 * cell gv 14 * cell gv 15 * cell gv 16 * cell gv 17 * cell gv 18 |-- encoded_at gv.
Proof.
  intros He. eapply derives_trans; [ | apply cells_encoded; auto ].
  unfold idx19. simpl. rewrite !sepcon_emp. cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* The globals in three chunks                                            *)
(* ---------------------------------------------------------------------- *)

(* The global variables of the program, in the order process_globals takes them, cut in three: A (the shim's
   state, four constants of punycode.c, encoded[], two blocks of the code under test), B (the 19 literals),
   C (points[], decoded[] and the other constants of punycode.c).  Each chunk is processed in a file of its
   own (RsmGlobA/B/C.v). *)
Definition vars : list (ident * globvar type) := ltac:(let x := eval vm_compute in (QPprog_vars p) in exact x).
Definition varsA : list (ident * globvar type) := ltac:(let x := eval vm_compute in (firstn 10 vars) in exact x).
Definition varsB : list (ident * globvar type) :=
  ltac:(let x := eval vm_compute in (firstn 19 (skipn 10 vars)) in exact x).
Definition varsC : list (ident * globvar type) := ltac:(let x := eval vm_compute in (skipn 29 vars) in exact x).

Lemma vars_split : QPprog_vars p = varsA ++ varsB ++ varsC.
Proof. vm_compute. reflexivity. Qed.

(* Rewriting the part already processed. *)
Lemma gip_derives Delta gv (done done': list mpred) rest:
  (forall rho, tc_environ Delta rho -> gvars_denote gv rho -> fold_right_sepcon done |-- fold_right_sepcon done') ->
  ENTAIL Delta, globvars_in_process gv done emp rest |-- globvars_in_process gv done' emp rest.
Proof.
  intros H rho. unfold globvars_in_process, local, lift1. simpl. normalize.
  apply sepcon_derives; [ apply (H rho); auto | auto ].
Qed.
