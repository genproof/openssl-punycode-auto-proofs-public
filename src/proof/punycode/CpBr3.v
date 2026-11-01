(* The 3-octet branch of codepoint2utf8 (0x800 <= c <= 0xFFFF), for BodyCp. *)
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

Lemma cp_branch3 {Espec: OracleKind} (DS: Maps.PTree.t funspec) (sh: share) (p: val) (old: list val) (c: Z) :
  writable_share sh -> Zlength old = 6 -> 2047 < c <= 65535 ->
  semax (cp_Delta DS)
    (PROP () LOCAL (temp _out p; temp _utf (Vlong (Int64.repr c))) SEP (data_at sh (tarray tuchar 6) old p))
    cp_br3 (cp_Post sh p c).
Proof.
  intros SH H Hc. unfold cp_Delta, cp_br3, cp_Post.
  match goal with |- semax ?D _ _ _ => pose (Delta := @abbreviate tycontext D); change D with Delta end.
  abbreviate_semax.
  forward. forward. forward. forward. forward.
  assert (U: utf8 c = [224 + c / 2 ^ 12 mod (15 + 1); 128 + c / 2 ^ 6 mod (63 + 1);
                       128 + c / 2 ^ 0 mod (63 + 1)]).
  { unfold utf8. destruct (Z.ltb_spec c 128); [lia|]. destruct (Z.ltb_spec c 2048); [lia|].
    destruct (Z.ltb_spec c 65536); [|lia].
    change (2 ^ 6) with 64; change (2 ^ 12) with 4096; change (15 + 1) with 16;
      change (63 + 1) with 64; change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite (Z.mod_small (c / 4096) 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    reflexivity. }
  cp_pre U. cpb c 12 15 224. cpb c 6 63 128. cpb c 0 63 128. cp_post c.
Qed.
