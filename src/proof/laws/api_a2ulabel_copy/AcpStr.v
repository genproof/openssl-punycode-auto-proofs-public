(* Law api_a2ulabel_copy: the string of the harness's buffer l ++ [0] (l any octets): its octets before the first
   NUL, whose position acp_first0 l is the value of n after the harness's loop `while (in[n] != 0) n++`. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.

(* The position of the first NUL of l (its length when it has none). *)
Fixpoint acp_first0 (l: list Z) : Z :=
  match l with [] => 0 | b :: r => if b =? 0 then 0 else 1 + acp_first0 r end.

Lemma acp_first0_range l: 0 <= acp_first0 l <= Zlength l.
Proof.
  induction l as [ | b r IH]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (b =? 0); lia.
Qed.

(* The octets before the first NUL are not 0. *)
Lemma acp_first0_nz l k: 0 <= k < acp_first0 l -> Znth k l <> 0.
Proof.
  revert k. induction l as [ | b r IH]; intros k Hk; simpl in Hk; [ lia | ].
  destruct (b =? 0) eqn:E; [ lia | ].
  destruct (Z.eq_dec k 0) as [-> | Nk].
  - rewrite Znth_0_cons. apply Z.eqb_neq in E; auto.
  - rewrite Znth_pos_cons by lia. apply IH. lia.
Qed.

Lemma acp_first0_at l: Znth (acp_first0 l) (l ++ [0]) = 0.
Proof.
  induction l as [ | b r IH]; simpl; [ reflexivity | ].
  destruct (b =? 0) eqn:E.
  - rewrite Znth_0_cons. apply Z.eqb_eq in E; auto.
  - pose proof (acp_first0_range r). rewrite Znth_pos_cons by lia.
    replace (1 + acp_first0 r - 1) with (acp_first0 r) by lia. exact IH.
Qed.

(* The string of l: its octets before the first NUL (none of them 0, so a C string). *)
Lemma acp_first0_str l: bytes_ok l -> OpensslPunycode.proof.shim.ShimSpec.str_ok (sublist 0 (acp_first0 l) l).
Proof.
  intros Hok. pose proof (acp_first0_range l).
  unfold OpensslPunycode.proof.shim.ShimSpec.str_ok. unfold bytes_ok in Hok.
  apply Forall_Znth. intros i Hi. rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia. rewrite Forall_Znth in Hok. specialize (Hok (i + 0) ltac:(lia)).
  pose proof (acp_first0_nz l (i + 0) ltac:(lia)). lia.
Qed.

(* The buffer l ++ [0] = the string, its NUL, then the rest. *)
Lemma acp_first0_split l:
  l ++ [0] = sublist 0 (acp_first0 l) l ++ [0] ++ sublist (acp_first0 l + 1) (Zlength l + 1) (l ++ [0]).
Proof.
  pose proof (acp_first0_range l). pose proof (acp_first0_at l) as Hz.
  rewrite <- Hz at 2. list_solve.
Qed.
