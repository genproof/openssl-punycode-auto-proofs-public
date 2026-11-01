(* Law api_a2ulabel_size: the string ossl_a2ulabel sees is the octets of the harness's buffer `in` (len octets bs,
   then the NUL the harness writes) up to its first NUL: first0 bs is the position of that NUL. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.

(* The position of the first NUL of l (its length when it has none). *)
Fixpoint first0 (l: list Z) : Z :=
  match l with [] => 0 | b :: r => if b =? 0 then 0 else 1 + first0 r end.

Lemma first0_range l: 0 <= first0 l <= Zlength l.
Proof.
  induction l as [ | b r IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (b =? 0); lia.
Qed.

Lemma first0_nz l: Forall (fun b => b <> 0) (sublist 0 (first0 l) l).
Proof.
  induction l as [ | b r IH]; simpl.
  - rewrite sublist_nil'; auto.
  - destruct (b =? 0) eqn:E.
    + rewrite sublist_nil'; auto.
    + pose proof (first0_range r).
      rewrite sublist_0_cons by lia. replace (1 + first0 r - 1) with (first0 r) by lia.
      constructor; auto. apply Z.eqb_neq in E; auto.
Qed.

Lemma first0_at l: Znth (first0 l) (l ++ [0]) = 0.
Proof.
  induction l as [ | b r IH]; simpl; [ reflexivity | ].
  destruct (b =? 0) eqn:E.
  - rewrite Znth_0_cons. apply Z.eqb_eq in E; auto.
  - pose proof (first0_range r). rewrite Znth_pos_cons by lia.
    replace (1 + first0 r - 1) with (first0 r) by lia. exact IH.
Qed.

(* The string of l: its octets before the first NUL (none of them 0, so a C string). *)
Lemma first0_str l: bytes_ok l -> OpensslPunycode.proof.shim.ShimSpec.str_ok (sublist 0 (first0 l) l).
Proof.
  intros Hok. pose proof (first0_nz l) as Hnz. pose proof (first0_range l).
  unfold OpensslPunycode.proof.shim.ShimSpec.str_ok. unfold bytes_ok in Hok.
  apply (Forall_sublist _ 0 (first0 l)) in Hok.
  rewrite Forall_forall in *. intros x Hx. specialize (Hok x Hx). specialize (Hnz x Hx). rep_lia.
Qed.

(* The buffer l ++ [0] = the string with its NUL, then the rest. *)
Lemma first0_split l:
  l ++ [0] = (sublist 0 (first0 l) l ++ [0]) ++ sublist (first0 l + 1) (Zlength l + 1) (l ++ [0]).
Proof.
  pose proof (first0_range l). pose proof (first0_at l) as Hz.
  rewrite <- Hz at 2. list_solve.
Qed.
