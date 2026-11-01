(* Law rfc_unique, model part 3: two successful runs of the main loop of Model.decode from the same state, with
   the same final output, read inputs of the same length whose octets from the start position on have the same
   digit-values (plain Coq). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqDigits.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunUniqInv.
Import ListNotations.
Local Open Scope Z_scope.

(* A successful run with enough fuel either stops at the end of the input with the output so far, or reads one
   delta and continues. *)
Lemma run_steps_case: forall inp f cap pos n i bias cur out,
  pos <= Zlength inp -> Zlength inp - pos <= Z.of_nat f ->
  steps inp f cap pos n i bias cur = (true, out) ->
  (Zlength inp = pos /\ out = cur) \/
  (pos < Zlength inp /\ exists f' i1 pos1, f = S f' /\
     digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1) /\
     steps inp f' cap pos1 (n + i1 / (Zlength cur + 1)) (i1 mod (Zlength cur + 1) + 1)
       (adapt (i1 - i) (Zlength cur + 1) (i =? 0))
       (insert_at (i1 mod (Zlength cur + 1)) (n + i1 / (Zlength cur + 1)) cur) = (true, out)).
Proof.
  intros inp f cap pos n i bias cur out Hp Hf H. destruct f as [|f].
  - left. cbn [steps] in H. inversion H; subst. simpl in Hf. split; [lia|reflexivity].
  - apply run_steps_S in H. destruct H as [[Hl ->]|[Hl [i1 [pos1 [Hd [_ Hs]]]]]].
    + left. split; [lia|reflexivity].
    + right. split; [exact Hl|]. exists f, i1, pos1. auto.
Qed.

(* A run that reads a delta outputs more than the output so far. *)
Lemma run_steps_grows: forall inp f cap pos n bias cur out i1,
  steps inp f cap pos (n + i1 / (Zlength cur + 1)) (i1 mod (Zlength cur + 1) + 1) bias
    (insert_at (i1 mod (Zlength cur + 1)) (n + i1 / (Zlength cur + 1)) cur) = (true, out) ->
  Zlength cur < Zlength out.
Proof.
  intros. apply run_steps_len in H.
  pose proof (Zlength_nonneg cur).
  pose proof (Z.mod_pos_bound i1 (Zlength cur + 1) ltac:(lia)).
  rewrite run_Zlength_insert in H by lia. lia.
Qed.

Lemma steps_unique: forall fA inpA fB inpB cap pos n i bias cur out,
  RunInv n i cur -> 0 <= pos -> pos <= Zlength inpA -> pos <= Zlength inpB ->
  Zlength inpA - pos <= Z.of_nat fA -> Zlength inpB - pos <= Z.of_nat fB ->
  steps inpA fA cap pos n i bias cur = (true, out) ->
  steps inpB fB cap pos n i bias cur = (true, out) ->
  Zlength inpA = Zlength inpB /\
  forall j, pos <= j < Zlength inpA ->
    digit_value (Znth j inpA) = digit_value (Znth j inpB) /\ digit_value (Znth j inpA) < 36.
Proof.
  intros fA. induction fA as [fA IH] using lt_wf_ind.
  intros inpA fB inpB cap pos n i bias cur out HI Hp HpA HpB HfA HfB HA HB.
  apply run_steps_case in HA; [|lia|lia]. apply run_steps_case in HB; [|lia|lia].
  destruct HA as [[HlA ->]|[HlA [fA' [i1A [posA [-> [HdA HsA]]]]]]];
  destruct HB as [[HlB HoB]|[HlB [fB' [i1B [posB [-> [HdB HsB]]]]]]].
  - split; [lia|]. intros j Hj; lia.
  - exfalso. apply run_steps_grows in HsB. lia.
  - exfalso. subst out. apply run_steps_grows in HsA. lia.
  - set (c := Zlength cur) in *.
    destruct (run_digits_shape inpA _ pos i 1 36 bias i1A posA ltac:(lia) Hp HdA) as [[XA [HXA HiA]] HposA].
    destruct (run_digits_shape inpB _ pos i 1 36 bias i1B posB ltac:(lia) Hp HdB) as [[XB [HXB HiB]] HposB].
    destruct (run_step_inv n i cur i1A HI ltac:(lia)) as [HIA [HnA [HprA HsmA]]].
    destruct (run_step_inv n i cur i1B HI ltac:(lia)) as [HIB [HnB [HprB HsmB]]].
    fold c in HIA, HnA, HprA, HsmA, HIB, HnB, HprB, HsmB.
    pose proof (run_steps_future inpA fA' cap posA _ _ _ _ out HIA ltac:(lia) HsA) as HFA.
    pose proof (run_steps_future inpB fB' cap posB _ _ _ _ out HIB ltac:(lia) HsB) as HFB.
    destruct (first_insertion_unique n i cur out _ _ _ _ HI HnA HprA HsmA HFA HnB HprB HsmB HFB)
      as [Hn Hpq].
    assert (Hi1: i1A = i1B).
    { assert (Hc: 0 <= c) by apply Zlength_nonneg.
      rewrite (Z.div_mod i1A (c + 1)) by lia. rewrite (Z.div_mod i1B (c + 1)) by lia.
      rewrite Hpq. f_equal. f_equal. lia. }
    rewrite <- Hi1 in HdB, HsB.
    destruct (run_digits_unique inpA _ inpB _ pos i 1 36 bias i1A posA posB ltac:(lia) Hp HdA HdB)
      as [<- Hdig].
    destruct (IH fA' ltac:(lia) inpA fB' inpB cap posA _ _ _ _ out HIA ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) HsA HsB) as [Hlen Hrest].
    split; [exact Hlen|].
    intros j Hj. destruct (Z_lt_le_dec j posA); [apply Hdig; lia | apply Hrest; lia].
Qed.
