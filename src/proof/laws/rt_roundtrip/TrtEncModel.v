(* Model facts for the body of the harness's encoder encode (TrtBodyEncode.v), beyond those of pr_encode's proof
   (EncModel.v): the minimum search of encode starts from UINT64_MAX where Model.min_ge starts from maxint + 1. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.EncModel.

(* For code points <= maxint, two starts above maxint give the same minimum, or both stay above maxint. *)
Lemma min_fold_big: forall n l a1 a2, Forall (fun c => 0 <= c <= maxint) l -> maxint < a1 -> maxint < a2 ->
  fold_left (min_step n) l a1 = fold_left (min_step n) l a2 \/
  (maxint < fold_left (min_step n) l a1 /\ maxint < fold_left (min_step n) l a2).
Proof.
  intros n l. induction l; simpl; intros. right; auto.
  inv H. rewrite !min_step_eq.
  destruct (n <=? a) eqn:E; simpl.
  - replace (a <? a1) with true by lia. replace (a <? a2) with true by lia. left; reflexivity.
  - apply IHl; auto.
Qed.

(* The minimum code point >= n found from UINT64_MAX is Model.min_ge when one exists. *)
Lemma min_ge_u64: forall cps n, Forall (fun c => 0 <= c <= maxint) cps -> (exists c, In c cps /\ n <= c) ->
  fold_left (min_step n) cps Int64.max_unsigned = min_ge cps n.
Proof.
  intros. unfold min_ge. fold (min_step n).
  destruct (min_fold_big n cps Int64.max_unsigned (maxint + 1) H) as [E | [E1 E2]];
    [unfold maxint; rep_lia | lia | auto |].
  exfalso. destruct H0 as [c [I N]]. destruct (min_fold_props n cps (maxint + 1)) as [_ [_ H3]].
  specialize (H3 c I N). rewrite Forall_forall in H. specialize (H c I). cbv zeta in H3. lia.
Qed.
