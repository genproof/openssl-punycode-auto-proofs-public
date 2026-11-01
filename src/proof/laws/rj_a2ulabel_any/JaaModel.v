(* Law rj_a2ulabel_any: the facts about the model that the law needs.  ossl_a2ulabel's result is -1, 0 or 1, and
   -1 when out is NULL or outlen is 0 (PunySpec.a2u_outcome); the string ossl_a2ulabel sees is the octets of the
   harness's buffer up to its first NUL (first0). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.

(* The conversion of a list of labels ends with -1, 0 or 1. *)
Lemma a2u_labels_res cap k ls:
  fst (a2u_labels cap k ls) = -1 \/ fst (a2u_labels cap k ls) = 0 \/ fst (a2u_labels cap k ls) = 1.
Proof.
  revert k. induction ls as [ | l ls IH]; intros k; simpl.
  - destruct (snd (put cap k [0])); simpl; auto.
  - destruct (label_step cap k l) as [ok k1]. destruct ok; simpl; auto.
    destruct ls as [ | l' ls'].
    + destruct (snd (put cap k1 [0])); simpl; auto.
    + apply IH.
Qed.

Lemma a2ulabel_res s cap:
  fst (a2ulabel s cap) = -1 \/ fst (a2ulabel s cap) = 0 \/ fst (a2ulabel s cap) = 1.
Proof.
  unfold a2ulabel. pose proof (a2u_labels_res cap ([], false) (labels s)) as H.
  destruct (a2u_labels cap ([], false) (labels s)). exact H.
Qed.

(* The result of ossl_a2ulabel by its specification: -1, 0 or 1; -1 for a NULL out or a zero outlen. *)
Lemma a2u_outcome_res out cap s init fn zf mf:
  let r := fst (fst (fst (OpensslPunycode.proof.punycode.PunySpec.a2u_outcome out cap s init fn zf mf))) in
  (r = 1 \/ r = 0 \/ r = -1) /\ (out = nullval \/ cap = 0 -> r = -1).
Proof.
  unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome.
  destruct (Val.eq out nullval); [ simpl; auto | ].
  destruct (cap =? 0) eqn:Ec; [ simpl; auto | ].
  destruct (negb (fn =? 0)); [ simpl; auto | ].
  destruct mf; [ simpl; auto | ].
  pose proof (a2ulabel_res s cap) as H. destruct (a2ulabel s cap) as [r w]. simpl in *.
  split; [ lia | ]. intros [E | E]; [ contradiction | subst; discriminate ].
Qed.

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
