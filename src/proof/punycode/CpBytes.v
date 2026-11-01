(* Helpers of the body of codepoint2utf8 (BodyCp, CpBr3, CpBr4): the octets, the branch statements. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.

(* Or-ing a lead/continuation marker onto small payload bits is addition (checked over the finite range). *)
Lemma lor_marker (j t y: Z) :
  forallb (fun y => Z.lor y t =? t + y) (map Z.of_nat (seq 0 (Z.to_nat (2 ^ j)))) = true ->
  0 <= y < 2 ^ j -> Z.lor y t = t + y.
Proof.
  intros Hb Hy. rewrite forallb_forall in Hb.
  specialize (Hb y). rewrite Z.eqb_eq in Hb. apply Hb.
  apply in_map_iff. exists (Z.to_nat y). split; [lia|].
  apply in_seq. lia.
Qed.

(* The octet (unsigned char)(((c >> k) & m) | t) of codepoint2utf8. *)
Lemma cp_byte0 (c k m j t: Z) :
  0 <= c <= Int64.max_unsigned -> 0 <= k < 64 -> m = Z.ones j -> 0 <= j <= 6 -> 0 <= t ->
  t + 2 ^ j <= 256 ->
  forallb (fun y => Z.lor y t =? t + y) (map Z.of_nat (seq 0 (Z.to_nat (2 ^ j)))) = true ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.lor (Int64.Z_mod_modulus
    (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus c) k)) m)) t))))
  = Int.repr (t + (c / 2 ^ k) mod 2 ^ j).
Proof.
  intros Hc Hk -> Hj Ht Hr Hb.
  assert (Hp: 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq: 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite !Int64.Z_mod_modulus_eq.
  change Int64.modulus with 18446744073709551616.
  change Int64.max_unsigned with 18446744073709551615 in Hc.
  rewrite (Z.mod_small c) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= c / 2 ^ k <= c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; nia).
  rewrite (Z.mod_small (c / 2 ^ k)) by lia.
  rewrite Z.land_ones by lia.
  assert (0 <= (c / 2 ^ k) mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small ((c / 2 ^ k) mod 2 ^ j)) by lia.
  rewrite (lor_marker j t) by auto.
  rewrite (Z.mod_small (t + _)) by lia.
  apply Int.same_if_eq. unfold Int.eq.
  rewrite !Int.zero_ext_mod by (cbn; lia).
  rewrite !Int.unsigned_repr by rep_lia.
  change (two_p 8) with 256.
  rewrite Z.mod_mod, Z.mod_small by lia. apply zeq_true.
Qed.

Lemma cp_byte (c k m t: Z) :
  0 <= c <= Int64.max_unsigned -> 0 <= k < 64 -> m = Z.ones (Z.log2 (m + 1)) -> 0 <= m <= 63 -> 0 <= t ->
  t + m + 1 <= 256 ->
  forallb (fun y => Z.lor y t =? t + y) (map Z.of_nat (seq 0 (Z.to_nat (m + 1)))) = true ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.lor (Int64.Z_mod_modulus
    (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus c) k)) m)) t))))
  = Int.repr (t + (c / 2 ^ k) mod (m + 1)).
Proof.
  intros Hc Hk Hm Hm' Ht Hr Hb.
  assert (Hj: 0 <= Z.log2 (m + 1) <= 6).
  { split; [apply Z.log2_nonneg|]. change 6 with (Z.log2 64). apply Z.log2_le_mono. lia. }
  assert (He: m + 1 = 2 ^ Z.log2 (m + 1)) by (rewrite Hm at 1; rewrite Z.ones_equiv; lia).
  rewrite He in Hb |- *. apply (cp_byte0 c k m); auto. lia.
Qed.

Lemma ze8 (v: Z) : 0 <= v < 256 -> Int.zero_ext 8 (Int.repr v) = Int.repr v.
Proof.
  intros. apply Int.same_if_eq. unfold Int.eq.
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite !Int.unsigned_repr by rep_lia.
  change (two_p 8) with 256. rewrite Z.mod_small by lia. apply zeq_true.
Qed.

Ltac cp_pre u :=
  match goal with |- data_at _ _ ?l _ |-- _ => Exists l end;
  entailer!;
  rewrite u.

Ltac cp_post c :=
  rewrite ?Int64.Z_mod_modulus_eq, ?(Z.mod_small c) by rep_lia;
  rewrite ?ze8 by lia;
  unfold vb; cbn [map]; split; [list_solve | reflexivity].

Ltac cpb c k m t := rewrite (cp_byte c k m t) by first [reflexivity | rep_lia].

(* The pieces of the function the branch lemmas are about: its type context (with the specs abstracted, as
   after start_function), the 3- and 4-octet branches, its postcondition. *)
Definition cp_Delta (DS: Maps.PTree.t funspec) : tycontext :=
  ltac:(let T := eval compute in (make_tycontext_t (fn_params f_codepoint2utf8) (fn_temps f_codepoint2utf8)) in
        let G := eval compute in (make_tycontext_g Vprog Gprog_none) in
        exact (mk_tycontext T (Maps.PTree.empty type) tint G DS (Maps.PTree.empty Annotation))).

Definition cp_br3 : statement :=
  ltac:(let s := eval cbv beta iota delta [f_codepoint2utf8 fn_body] in
          (match fn_body f_codepoint2utf8 with
           | Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ s _)) => s | _ => Sskip end) in exact s).

Definition cp_br4 : statement :=
  ltac:(let s := eval cbv beta iota delta [f_codepoint2utf8 fn_body] in
          (match fn_body f_codepoint2utf8 with
           | Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ s _))) => s | _ => Sskip end)
        in exact s).

Definition cp_Post (sh: share) (p: val) (c: Z) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
      (EX new: list val,
       PROP (Zlength new = 6; sublist 0 (Zlength (utf8 c)) new = vb (utf8 c))
       RETURN (Vint (Int.repr (Zlength (utf8 c))))
       SEP (data_at sh (tarray tuchar 6) new p))%argsassert)
    (stackframe_of f_codepoint2utf8).
