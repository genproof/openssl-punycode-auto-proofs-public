(* The round trip of law rt_roundtrip in the model (TrtModelStmt.trt_model_stmt), for any number of code points:
   the decoder, started as Model.decode starts it on an encoding, follows the encoder (TrtSim.sim_rounds_any). *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSim.
Import ListNotations.
Local Open Scope Z_scope.

Theorem trt_model : trt_model_stmt.
Proof.
  intros cps e Hcps He.
  destruct (encode_shape cps e Hcps He) as [r [Er [Dr Lr]]].
  set (basics := filter (fun c => c <? 128) cps) in *.
  set (b := Zlength basics) in *.
  set (out0 := if 0 <? b then basics ++ [45] else basics) in *.
  assert (Hb0: 0 <= b) by apply Zlength_nonneg.
  assert (Hbl: b <= Zlength cps) by apply Zlength_filter_le.
  assert (Hout0: b <= Zlength out0)
    by (subst out0; destruct (0 <? b); [rewrite Zlength_app, Zlength_cons, Zlength_nil|]; lia).
  split.
  { rewrite Er, Zlength_app. lia. }
  assert (Hld: last_delim e = b).
  { unfold last_delim. rewrite Er. subst out0. destruct (0 <? b) eqn:Eb.
    - rewrite <- app_assoc, last_delim_from_app. cbn [app last_delim_from].
      rewrite Z.eqb_refl, last_delim_from_none; auto.
    - apply Z.ltb_ge in Eb. assert (basics = []) by (apply Zlength_nil_inv; lia).
      rewrite H. cbn [app]. rewrite last_delim_from_none; auto. subst b; rewrite H; auto. }
  assert (Hbas: Forall (fun c => c < 128) basics)
    by (eapply Forall_impl; [|apply filter_basic]; simpl; intros a [Ha _]; auto).
  assert (Hpre: sublist 0 b e = basics).
  { rewrite Er. subst out0. destruct (0 <? b); [rewrite <- app_assoc|];
      rewrite sublist_app1 by (subst b; lia); apply sublist_same; auto. }
  assert (Hgood: sim_good cps (decode e (Zlength cps))).
  { unfold decode. rewrite Hld, Hpre, basic_prefix_all by auto.
    rewrite (proj2 (Z.ltb_ge (Zlength cps) b)) by lia. rewrite Z.ltb_irrefl.
    replace (if b =? 0 then 0 else b + 1) with (Zlength out0).
    2:{ subst out0. destruct (0 <? b) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
        - rewrite (proj2 (Z.eqb_neq b 0)) by lia. rewrite Zlength_app, Zlength_cons, Zlength_nil. auto.
        - rewrite (proj2 (Z.eqb_eq b 0)) by lia. subst b; lia. }
    unfold encode in He. fold basics b out0 in He.
    apply (sim_rounds_any cps e (Zlength cps) b Hcps ltac:(lia) (S (length cps)) 128 0 72 b out0 128 0 He);
      auto; try lia.
    rewrite <- Zlength_correct. rewrite Er, Zlength_app. pose proof (Zlength_nonneg out0). lia. }
  destruct Hgood as [Hg|[Hg NB]].
  - rewrite Hg. split; auto.
  - split; [intros Ht; congruence|]. intros HB. exfalso. apply NB. exact HB.
Qed.
