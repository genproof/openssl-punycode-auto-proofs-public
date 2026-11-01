(* pr_encode: one iteration of the pass, after the code point c is loaded: the case n <= c. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncDig.
Require Import OpensslPunycode.proof.harness.EncPassLt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Local Opaque enc_digits adapt.

Lemma enc_pass_ge: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (f: nat) (n h0 B j c delta bias h: Z)
  (out: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Zlength cps <= Int.max_unsigned -> 0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  0 <= j < Zlength cps -> 0 <= h0 <= Zlength cps -> 0 <= B <= Int.max_unsigned -> 0 <= n <= maxint ->
  n <= c ->
  encode cps = kont cps f n (c :: sublist (j + 1) (Zlength cps) cps) delta bias h B out ->
  h = h0 + cnt_eq n (sublist 0 j cps) -> 0 <= delta <= maxint -> 0 <= bias <= 2400 -> Zlength out <= ocap ->
  0 <= c <= Int.max_unsigned ->
  cnt_eq n (sublist 0 (j + 1) cps) = cnt_eq n (sublist 0 j cps) + (if c =? n then 1 else 0) ->
  cnt_eq n (sublist 0 j cps) <= j - 0 -> 0 <= cnt_eq n (sublist 0 j cps) ->
  semax DeltaE
   (PROP () LOCAL (temp _c (Vlong (Int64.repr c)); temp _t'7 (Vint (Int.repr c));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_passrest
   (overridePost (pass_st shc pc cps sho po ocap oinit shl pl f n h0 B (j + 1) j)
      (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros until out. intros H H0 H1 H3 H4 H5 H6 H7 H8 H9 Hge Hk Hh Hd Hb Ho Hc Hcnt Hcl Hcn0.
  pose proof (Zlength_nonneg out) as Hol.
  unfold stmt_passrest, pass_st, enc_post. abbreviate_semax.
forward_if (PROP ()
    LOCAL (temp _c (Vlong (Int64.repr c)); temp _n (Vlong (Int64.repr n));
      temp _delta (Vlong (Int64.repr delta)); temp _bias (Vlong (Int64.repr bias));
      temp _out (Vlong (Int64.repr (Zlength out))); temp _b (Vlong (Int64.repr B));
      temp _h (Vlong (Int64.repr h)); temp _j (Vlong (Int64.repr j)); temp _cps pc;
      temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po; temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
      data_at_ shl tulong pl)).
  { fix_cmp. lia. }
  { forward. entailer!. }
  forward_if.
  + fix_eq64. assert (Hcn: c = n) by assumption. rewrite Hcn in Hk. rewrite kont_eq in Hk.
    eapply semax_pre; [ | eapply semax_post; [ | | | | eapply (enc_dig shc pc cps sho po ocap oinit shl pl
       n delta bias h B j out f (sublist (j + 1) (Zlength cps) cps)) ] ].
    { entailer!. }
    { rewrite !HoP. unfold dig_q.
      Exists 0 (adapt delta (h + 1) (h =? B)) (h + 1) (out ++ enc_digits 64 delta 36 bias). entailer!.
      split; [rewrite Hcnt, Z.eqb_refl; lia | apply adapt_bound; lia]. }
    { apply brk_post. }
    { apply cont_post. }
    { intros. apply ENTAIL_refl. }
    all: auto; try lia.
  + assert (Hne: c <> n) by (intro E; match goal with H: Int64.repr c <> Int64.repr n |- _ => apply H end;
      rewrite E; reflexivity).
    rewrite kont_gt in Hk by lia.
    forward. Exists delta bias h out. entailer!.
    rewrite Hcnt. replace (c =? n) with false by lia. lia.
Qed.
