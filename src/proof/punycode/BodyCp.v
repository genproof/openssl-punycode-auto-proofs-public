(* The body of codepoint2utf8 (crypto/punycode.c), under Punycode.CS. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.punycode.code.
Require Import OpensslPunycode.proof.punycode.CpBytes.
Require Import OpensslPunycode.proof.punycode.CpBr3.
Require Import OpensslPunycode.proof.punycode.CpBr4.

(* simpl (in VST's expression evaluation) unfolds Z.shiftr into Pos.iter: exponential in the shift. *)
Local Opaque Z.shiftr.

Lemma body_cp2utf8_proof : semax_body Vprog Gprog_none f_codepoint2utf8 codepoint2utf8_spec.
Proof.
start_function.
forward_if.
{ rewrite !Int64.unsigned_repr in H1 by rep_lia.
  assert (U: utf8 c = [c]) by (unfold utf8; destruct (Z.ltb_spec c 128); [reflexivity | lia]).
  forward. forward. forward. cp_pre U. cp_post c. }
rewrite !Int64.unsigned_repr in H1 by rep_lia.
forward_if.
{ rewrite !Int64.unsigned_repr in H2 by rep_lia.
  forward. forward. forward. forward.
  assert (U: utf8 c = [192 + c / 2 ^ 6 mod (31 + 1); 128 + c / 2 ^ 0 mod (63 + 1)]).
  { unfold utf8. destruct (Z.ltb_spec c 128); [lia|]. destruct (Z.ltb_spec c 2048); [|lia].
    change (2 ^ 6) with 64; change (31 + 1) with 32; change (63 + 1) with 64; change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite (Z.mod_small (c / 64) 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    reflexivity. }
  cp_pre U. cpb c 6 31 192. cpb c 0 63 128. cp_post c. }
rewrite !Int64.unsigned_repr in H2 by rep_lia.
forward_if.
{ rewrite !Int64.unsigned_repr in H3 by rep_lia. apply (cp_branch3 Delta_specs); auto; lia. }
rewrite !Int64.unsigned_repr in H3 by rep_lia.
forward_if.
{ rewrite !Int64.unsigned_repr in H4 by rep_lia. apply (cp_branch4 Delta_specs); auto; lia. }
rewrite !Int64.unsigned_repr in H4 by rep_lia.
assert (U: utf8 c = []).
{ unfold utf8. destruct (Z.ltb_spec c 128); [lia|]. destruct (Z.ltb_spec c 2048); [lia|].
  destruct (Z.ltb_spec c 65536); [lia|]. destruct (Z.leb_spec c 1114111); [lia|]. reflexivity. }
forward. forward. forward. forward. forward.
cp_pre U. split; [list_solve | reflexivity].
Qed.
