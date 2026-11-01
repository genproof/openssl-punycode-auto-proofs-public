(* The body of last_delimiter (harness/laws_common.h): one pass over the n octets, remembering the last '-'. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.punycode.DecModel.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Lemma body_last_delimiter : semax_body Vprog Gprog_none f_last_delimiter last_delimiter_spec.
Proof.
  start_function.
  forward.
  destruct (Z.eq_dec (Zlength l) 0) as [E|E].
  { assert (l = []) by (apply Zlength_nil_inv; auto). subst l.
    unfold arr0. simpl.
    forward_for_simple_bound 0 (EX i: Z, PROP () LOCAL (temp _last (Vlong (Int64.repr 0)); temp _s s;
        temp _n (Vlong (Int64.repr 0))) SEP ()).
    all: try (simpl in *; lia).
    - entailer!.
    - forward. }
  unfold arr0. rewrite !if_false by auto.
  forward_for_simple_bound (Zlength l) (EX i: Z, PROP ()
    LOCAL (temp _last (Vlong (Int64.repr (last_delim (sublist 0 i l)))); temp _s s;
           temp _n (Vlong (Int64.repr (Zlength l))))
    SEP (data_at sh (tarray tuchar (Zlength l)) (vb l) s)).
  - entailer!.
  - assert (Ha: 0 <= Znth i l <= 255) by (apply (proj1 (Forall_Znth _ _) H); lia).
    assert (HZa: Znth i (vb l) = Vint (Int.repr (Znth i l))) by (unfold vb; rewrite Znth_map by lia; auto).
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZa. simpl.
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZa.
    forward_if.
    + forward. entailer!.
      rewrite last_delim_snoc by lia. rewrite (proj2 (Z.eqb_eq _ _)) by auto. auto.
    + forward. entailer!.
      rewrite last_delim_snoc by lia. rewrite (proj2 (Z.eqb_neq _ _)) by (intro X; apply H2; rewrite X; auto).
      auto.
  - forward. entailer!.
    { rewrite sublist_same by lia. auto. }
    unfold arr0. rewrite !if_false by auto. cancel.
Qed.
