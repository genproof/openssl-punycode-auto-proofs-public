(* Lemmas and tactics for the body of pr_utf8 (BodyRtUtf8*.v, part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.

Lemma zext8_mod: forall x, Int.zero_ext 8 (Int.repr x) = Int.repr (x mod 256).
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (split; [lia | reflexivity]).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 8) with 256.
  symmetry. apply Zmod_div_mod; try rep_lia. apply Z.mod_divide; [lia | reflexivity].
Qed.

Lemma mod64_mod256: forall x, Int64.Z_mod_modulus x mod 256 = x mod 256.
Proof.
  intros. rewrite Int64.Z_mod_modulus_eq. symmetry. apply Zmod_div_mod; try rep_lia.
  apply Z.mod_divide; [lia | reflexivity].
Qed.

Lemma upd_1: forall (old: list val) v0, Zlength old = 1 -> upd_Znth 0 old v0 = [v0].
Proof. intros. list_solve. Qed.
Lemma upd_2: forall (old: list val) v0 v1, Zlength old = 2 -> upd_Znth 1 (upd_Znth 0 old v0) v1 = [v0; v1].
Proof. intros. list_solve. Qed.
Lemma upd_3: forall (old: list val) v0 v1 v2, Zlength old = 3 ->
  upd_Znth 2 (upd_Znth 1 (upd_Znth 0 old v0) v1) v2 = [v0; v1; v2].
Proof. intros. list_solve. Qed.
Lemma upd_4: forall (old: list val) v0 v1 v2 v3, Zlength old = 4 ->
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 old v0) v1) v2) v3 = [v0; v1; v2; v3].
Proof. intros. list_solve. Qed.

(* The octets stored by pr_utf8, as computed by forward, are the model's. *)
Ltac utf8_vals :=
  repeat match goal with |- context [let (q, _) := Z.div_eucl ?x ?y in q] =>
    change (let (q, _) := Z.div_eucl x y in q) with (x / y) end;
  rewrite ?zext8_mod, ?Int64.Z_mod_modulus_eq;
  change Int64.modulus with 18446744073709551616.

Ltac utf8_fin c :=
  unfold vb; simpl map; utf8_vals;
  match goal with |- data_at _ _ ?L1 _ |-- data_at _ _ ?L2 _ => replace L1 with L2; [apply derives_refl|] end;
  repeat match goal with
  | |- (_ :: _) = (_ :: _) => f_equal
  | |- Vint (Int.repr _) = Vint (Int.repr _) => do 2 f_equal
  end;
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ <= _ => fail 1 | _ < _ => fail 1 | _ >= _ => fail 1 | _ <= _ <= _ => fail 1 | _ <= _ < _ => fail 1
    | _ => clear H
    end
  end;
  rewrite ?(Z.mod_small c 18446744073709551616) by rep_lia;
  Z.to_euclidean_division_equations; lia.

