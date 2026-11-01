(* pr_decode: the main loop (one delta per iteration: DRDigits, then DRRest). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.DRInv.
Local Open Scope logic.
Require Import OpensslPunycode.proof.harness.DRDigits.
Require Import OpensslPunycode.proof.harness.DRRest.

Lemma loop_block: forall (Espec: OracleKind) shi pin inp sho pout cap (init: list val) shd pd,
  readable_share shi -> writable_share sho -> writable_share shd -> bytes_ok inp ->
  Zlength inp < Int.max_unsigned -> 0 <= cap <= Int.max_unsigned -> Zlength init = cap ->
  Forall (fun c => c < 128) (sublist 0 (last_delim inp) inp) -> last_delim inp <= cap ->
  semax (func_tycontext f_pr_decode Vprog Gprog_decode nil)
  (PROP ()
   LOCAL (temp _bias (Vlong (Int64.repr 72)); temp _i (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr 128));
     temp _pos (Vlong (Int64.repr (if last_delim inp =? 0 then 0 else last_delim inp + 1))); temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
   SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
        arr0 sho tuint cap (vb (sublist 0 (last_delim inp) inp) ++ sublist (last_delim inp) cap init) pout;
        data_at shd t_dec (dec_rep 0 (last_delim inp)) pd))
  stmt_main
  (overridePost
    (EX out: list Z,
     PROP (decode inp cap = (true, out))
     LOCAL (temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
     SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd))
    (dr_post shi pin inp sho pout cap init shd pd)).
Proof.
intros Espec shi pin inp sho pout cap init shd pd SH SH0 SH1 H LEN2 H1 H2 H3 H4.
assert (LEN: 0 <= Zlength inp) by apply Zlength_nonneg.
unfold stmt_main, dr_post. abbreviate_semax.
forward_while (dr_inv shi pin inp sho pout cap init shd pd).
{ pose proof (last_delim_range inp) as LD.
  unfold dr_inv.
  Exists (if last_delim inp =? 0 then 0 else last_delim inp + 1) 128 0 72 (sublist 0 (last_delim inp) inp) (length inp).
  rewrite Zlength_sublist by lia.
  entailer!.
  rewrite <- decode_basic by auto. rewrite <- Zlength_correct.
  destruct (last_delim inp =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; repeat split; unfold maxint; lia.
  apply derives_refl. }
{ entailer!. }
{ assert (POS: pos < Zlength inp)
    by (unfold Int64.ltu in HRE; rewrite !Int64.unsigned_repr in HRE by rep_lia; destruct zlt; [lia | discriminate]).
  forward. forward. forward.
  change (Int.signed (Int.repr 1)) with 1.
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_seq.
  { apply (digits_block Espec shi pin inp sho pout cap init shd pd pos n i bias out f); auto; unfold maxint in *; rep_lia. }
  unfold dig_brk. Intros i1 pos1.
  apply (rest_block Espec shi pin inp sho pout cap init shd pd pos n i bias out f i1 pos1); try lia; auto.
  unfold dr_inv. Intros pos' n' i' bias' out' f'. Exists (pos', n', i', bias', out', f'). simpl. entailer!. }
assert (POS: Zlength inp <= pos)
  by (unfold Int64.ltu in HRE; rewrite !Int64.unsigned_repr in HRE by rep_lia; destruct zlt; [discriminate | lia]).
assert (DT: decode inp cap = (true, out))
  by (match goal with D: decode _ _ = steps _ _ _ _ _ _ _ _ |- _ => rewrite D end; apply steps_done; lia).
forward. Exists out. entailer!.
Qed.
