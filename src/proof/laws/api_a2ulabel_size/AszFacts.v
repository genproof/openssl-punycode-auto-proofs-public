(* Law api_a2ulabel_size: what the two calls of ossl_a2ulabel give by its specification (PunySpec.a2u_outcome), in
   the form the main uses: the result is -1, 0 or 1; the failure flag of the shim stays 0 only when the WPACKET
   record was allocated, and then the result and the octets are the model's; and the law's model facts
   (AszNul, AszMono) put together for the state after the test of the first result. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszNul.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMono.

(* The conversion of a list of labels ends with -1, 0 or 1. *)
Lemma asz_labels_res cap k ls:
  fst (a2u_labels cap k ls) = -1 \/ fst (a2u_labels cap k ls) = 0 \/ fst (a2u_labels cap k ls) = 1.
Proof.
  revert k. induction ls as [ | l ls IH]; intros k; simpl.
  - destruct (snd (put cap k [0])); simpl; auto.
  - destruct (label_step cap k l) as [ok k1]. destruct ok; simpl; auto.
    destruct ls as [ | l' ls'].
    + destruct (snd (put cap k1 [0])); simpl; auto.
    + apply IH.
Qed.

Lemma asz_a2ulabel_res s cap:
  fst (a2ulabel s cap) = -1 \/ fst (a2ulabel s cap) = 0 \/ fst (a2ulabel s cap) = 1.
Proof.
  unfold a2ulabel. pose proof (asz_labels_res cap ([], false) (labels s)) as H.
  destruct (a2u_labels cap ([], false) (labels s)). exact H.
Qed.

(* One call with a non-NULL out and the knob of the shim at 0. *)
Lemma asz_outcome out cap s init zf mf r fn' zf' ov:
  out <> nullval ->
  OpensslPunycode.proof.punycode.PunySpec.a2u_outcome out cap s init 0 zf mf = (r, fn', zf', ov) ->
  fn' = 0 /\ (r = -1 \/ r = 0 \/ r = 1) /\ (zf' = zf \/ zf' = 1) /\
  (zf' = 0 -> cap <> 0 -> zf = 0 /\ r = fst (a2ulabel s cap) /\
     ov = vb (snd (a2ulabel s cap)) ++ sublist (Zlength (snd (a2ulabel s cap))) cap init) /\
  (cap = 0 -> r = -1).
Proof.
  intros Hout E. unfold OpensslPunycode.proof.punycode.PunySpec.a2u_outcome in E.
  destruct (Val.eq out nullval); [ contradiction | ].
  destruct (cap =? 0) eqn:Ec.
  { inversion E; subst. apply Z.eqb_eq in Ec. split; auto. split; auto. split; auto. split; [ | auto ].
    intros _ C. contradiction. }
  apply Z.eqb_neq in Ec. simpl in E.
  destruct mf.
  { inversion E; subst. split; auto. split; auto. split; auto. split; [ | intros; contradiction ].
    intros C. discriminate. }
  pose proof (asz_a2ulabel_res s cap) as Hr.
  destruct (a2ulabel s cap) as [r0 w] eqn:A. inversion E; subst. simpl in Hr |- *.
  split; auto. split; auto. split; auto. split; [ | intros; contradiction ]. auto.
Qed.

(* After the test: the first call gave 1 into biglen octets (w' then its NUL); the second, into outlen >= 1 octets,
   gave r and the octets w2 then the rest of out. *)
Lemma asz_after s biglen outlen r2 w2 w init:
  OpensslPunycode.proof.shim.ShimSpec.str_ok s -> 0 < biglen -> 0 < outlen ->
  a2ulabel s biglen = (1, w) -> a2ulabel s outlen = (r2, w2) ->
  exists w', w = w' ++ [0] /\ Forall (fun b => 1 <= b <= 255) w' /\ Zlength w' + 1 <= biglen /\
    (Zlength w' + 1 <= outlen -> r2 = 1 /\ sublist 0 (Zlength w' + 1) (vb w2 ++ init) = vb (w' ++ [0])) /\
    (outlen < Zlength w' + 1 -> r2 = 0).
Proof.
  intros Hs Hb Ho A1 A2.
  destruct (a2ulabel_one_shape s biglen w Hs ltac:(lia) A1) as [Hl [w' [-> F]]].
  assert (Hw: Zlength (w' ++ [0]) = Zlength w' + 1) by list_solve.
  exists w'. split; auto. split; auto. split; [ lia | split ].
  - intros Hle. rewrite (a2ulabel_fit s biglen outlen (w' ++ [0]) A1 ltac:(lia)) in A2.
    inversion A2; subst. split; auto. unfold vb. list_solve.
  - intros Hlt. pose proof (a2ulabel_short s biglen outlen (w' ++ [0]) ltac:(lia) ltac:(lia) A1 ltac:(lia)) as H.
    rewrite A2 in H. exact H.
Qed.
