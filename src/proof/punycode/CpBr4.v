(* The 4-octet branch of codepoint2utf8 (0x10000 <= c <= 0x10FFFF), for BodyCp. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.CpBytes.

(* simpl (in VST's expression evaluation) unfolds Z.shiftr into Pos.iter: exponential in the shift. *)
Local Opaque Z.shiftr.

Lemma cp_branch4 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (sh: share) (p: val) (old: list val) (c: Z) :
  writable_share sh -> Zlength old = 6 -> 65535 < c <= 1114111 ->
  semax (cp_Delta DS)
    (PROP () LOCAL (temp _out p; temp _utf (Vlong (Int64.repr c))) SEP (data_at sh (tarray tuchar 6) old p))
    cp_br4 (cp_Post sh p c).
Proof.
  intros SH H Hc. unfold cp_Delta, cp_br4, cp_Post.
  match goal with |- semax ?D _ _ _ => pose (Delta := @abbreviate tycontext D); change D with Delta end.
  abbreviate_semax.
  assert (U: utf8 c = [240 + c / 2 ^ 18 mod (7 + 1); 128 + c / 2 ^ 12 mod (63 + 1);
                       128 + c / 2 ^ 6 mod (63 + 1); 128 + c / 2 ^ 0 mod (63 + 1)]).
  { unfold utf8. destruct (Z.ltb_spec c 128); [lia|]. destruct (Z.ltb_spec c 2048); [lia|].
    destruct (Z.ltb_spec c 65536); [lia|]. destruct (Z.leb_spec c 1114111); [|lia].
    change (2 ^ 6) with 64; change (2 ^ 12) with 4096; change (2 ^ 18) with 262144;
      change (7 + 1) with 8; change (63 + 1) with 64; change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite (Z.mod_small (c / 262144) 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    reflexivity. }
  forward. forward. forward. forward.
  (* Hide the contents for the last store and the return: the kernel check of that store on the explicit
     octets is slow. *)
  match goal with |- context [data_at _ _ ?l p] =>
    set (L := l) in *; assert (HL: L = l /\ True) by (split; [reflexivity | exact I]); clearbody L end.
  forward. forward.
  destruct HL as [HL _]; subst L.
  cp_pre U. cpb c 18 7 240. cpb c 12 63 128. cpb c 6 63 128. cpb c 0 63 128. cp_post c.
Qed.
