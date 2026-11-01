(* The body of copy_bytes (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

Lemma body_copy_bytes' : semax_body Vprog Gprog_none f_copy_bytes copy_bytes_spec.
Proof.
  start_function.
  destruct (Z.eq_dec (Zlength l) 0) as [E|E].
  { rewrite E in *. unfold arr0. simpl.
    forward_for_simple_bound 0 (EX i: Z, PROP () LOCAL (temp _d d; temp _s s;
        temp _n (Vlong (Int64.repr 0))) SEP ()).
    all: try lia.
    - entailer!.
    - unfold arr0. rewrite !if_true by auto. entailer!. }
  unfold arr0. rewrite !if_false by auto.
  forward_for_simple_bound (Zlength l) (EX i: Z, PROP () LOCAL (temp _d d; temp _s s;
      temp _n (Vlong (Int64.repr (Zlength l))))
    SEP (data_at shd (tarray tuchar (Zlength l)) (sublist 0 i (vb l) ++ sublist i (Zlength l) dold) d;
         data_at shs (tarray tuchar (Zlength l)) (vb l) s)).
  - entailer!. autorewrite with sublist. auto.
  - assert (Hb: 0 <= Znth i l <= 255) by (apply (proj1 (Forall_Znth _ _) H); lia).
    assert (HZ: Znth i (vb l) = Vint (Int.repr (Znth i l))) by (unfold vb; rewrite Znth_map by lia; auto).
    forward.
    { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZ. simpl.
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward. entailer!.
    list_solve.
  - entailer!. unfold arr0. rewrite !if_false by auto.
    rewrite sublist_same by (rewrite ?Zlength_vb; lia). rewrite ?sublist_nil, ?app_nil_r. cancel.
Qed.
