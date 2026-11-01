(* The body of same_bytes (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

Lemma body_same_bytes' : semax_body Vprog Gprog_none f_same_bytes same_bytes_spec.
Proof.
  start_function.
  destruct (Z.eq_dec (Zlength la) 0) as [E|E].
  { assert (la = []) by (apply Zlength_nil_inv; auto).
    assert (lb = []) by (apply Zlength_nil_inv; lia). subst la lb.
    unfold arr0. simpl.
    forward_for_simple_bound 0 (EX i: Z, PROP () LOCAL (temp _a a; temp _b b;
        temp _n (Vlong (Int64.repr 0))) SEP ()).
    all: try (simpl in *; lia).
    - entailer!.
    - forward. }
  unfold arr0. rewrite !if_false by auto.
  forward_for_simple_bound (Zlength la) (EX i: Z, PROP (sublist 0 i la = sublist 0 i lb)
    LOCAL (temp _a a; temp _b b; temp _n (Vlong (Int64.repr (Zlength la))))
    SEP (data_at sha (tarray tuchar (Zlength la)) (vb la) a;
         data_at shb (tarray tuchar (Zlength la)) (vb lb) b)).
  - entailer!.
  - assert (Ha: 0 <= Znth i la <= 255) by (apply (proj1 (Forall_Znth _ _) H); lia).
    assert (Hb: 0 <= Znth i lb <= 255) by (apply (proj1 (Forall_Znth _ _) H0); lia).
    assert (HZa: Znth i (vb la) = Vint (Int.repr (Znth i la))) by (unfold vb; rewrite Znth_map by lia; auto).
    assert (HZb: Znth i (vb lb) = Vint (Int.repr (Znth i lb))) by (unfold vb; rewrite Znth_map by lia; auto).
    cbv beta. Intros.
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZa. simpl.
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZb. simpl.
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZa, HZb.
    forward_if.
    + forward. rewrite if_false.
      { entailer!. unfold arr0. rewrite !if_false by auto. cancel. }
      intro Eq. subst lb. apply H5. auto.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1) la), (sublist_split 0 i (i+1) lb) by lia.
      rewrite H4, !sublist_len_1 by lia. rewrite H5. auto.
  - forward. rewrite if_true.
    { entailer!. unfold arr0. rewrite !if_false by auto. cancel. }
    rewrite !sublist_same in H3 by lia. auto.
Qed.
