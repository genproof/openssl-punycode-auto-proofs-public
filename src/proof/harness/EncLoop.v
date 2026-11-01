(* pr_encode: the pass over the code points for code point n (the for loop). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.proof.harness.EncDefs2.
Require Import OpensslPunycode.proof.harness.EncPassLt.
Require Import OpensslPunycode.proof.harness.EncPass.
Require Import OpensslPunycode.proof.harness.EncDefs3.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Local Open Scope logic.

Lemma enc_passloop: forall {Espec: OracleKind} shc pc cps sho po ocap oinit shl pl (f: nat) (n h0 B delta bias: Z)
  (out: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> Zlength cps <= Int.max_unsigned ->
  0 <= ocap <= Int64.max_unsigned -> Zlength oinit = ocap ->
  0 <= h0 <= Zlength cps -> 0 <= B <= Int.max_unsigned -> 0 <= n <= maxint ->
  encode cps = kont cps f n cps delta bias h0 B out ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> Zlength out <= ocap ->
  semax DeltaE
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _out (Vlong (Int64.repr (Zlength out)));
      temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h0));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
      temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out ocap oinit) po;
         data_at_ shl tulong pl))
   stmt_passloop
   (overridePost
     (EX delta': Z, EX bias': Z, EX h: Z, EX out': list Z,
      PROP (encode cps = enc_rounds cps f (n + 1) (delta' + 1) bias' h B out';
            (h = h0 + cnt_eq n cps)%Z; 0 <= delta' <= maxint; 0 <= bias' <= 2400; Zlength out' <= ocap)
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta'));
         temp _bias (Vlong (Int64.repr bias')); temp _out (Vlong (Int64.repr (Zlength out')));
         temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out' ocap oinit) po;
         data_at_ shl tulong pl))
     (enc_post shc pc cps sho po ocap oinit shl pl)).
Proof.
  intros. unfold stmt_passloop, enc_post. abbreviate_semax.
  forward_for_simple_bound (Zlength cps) (EX j: Z, EX delta': Z, EX bias': Z, EX h: Z, EX out': list Z,
      PROP (encode cps = kont cps f n (sublist j (Zlength cps) cps) delta' bias' h B out';
            (h = h0 + cnt_eq n (sublist 0 j cps))%Z; 0 <= delta' <= maxint; 0 <= bias' <= 2400;
            Zlength out' <= ocap)
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta'));
         temp _bias (Vlong (Int64.repr bias')); temp _out (Vlong (Int64.repr (Zlength out')));
         temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _o po;
         temp _ocap (Vlong (Int64.repr ocap)); temp _olen pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (bufv out' ocap oinit) po;
         data_at_ shl tulong pl)).
  { Exists delta bias h0 out. entailer!. rewrite sublist_same by lia.
    first [exact H9 | split; [exact H9 | rewrite sublist_nil; unfold cnt_eq; simpl; rewrite Zlength_nil; lia]]. }
  { rename i into j. cbv beta. Intros delta' bias' h out'.
    eapply semax_pre; [ | eapply semax_post; [ | | | | apply (enc_pass_body shc pc cps sho po ocap oinit shl pl f n h0 B j) ] ].
    { unfold pass_st. Exists delta' bias' h out'. entailer!. }
    { rewrite HoP. unfold pass_st. Intros d b h' o'. Exists d b h' o'. entailer!. }
    { unfold enc_post. simpl. intros; apply andp_left2. normalize. }
    { unfold enc_post. simpl. intros; apply andp_left2. normalize. }
    { intros. apply ENTAIL_refl. }
    all: auto; try lia. }
  Intros delta' bias' h out'. Exists delta' bias' h out'. entailer!.
  rewrite sublist_nil, sublist_same in * by lia. split; auto.
Qed.
