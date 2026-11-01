(* ossl_a2ulabel, ACE branch: the model facts of the decoding step (plain Coq). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uAceRange.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uAceDefs.

(* The A-label at st: its index range in s. *)
Lemma ace_idx: forall s st,
  0 <= st <= Zlength s -> is_ace (label_of (rest_at s st)) = true ->
  4 <= index_of 46 (rest_at s st) /\ st + index_of 46 (rest_at s st) <= Zlength s /\
  ace_in (rest_at s st) = sublist (st + 4) (st + index_of 46 (rest_at s st)) (s ++ [0]).
Proof.
  intros s st Hst HA.
  pose proof (index_of_range 46 (rest_at s st)) as R.
  unfold rest_at in *. rewrite Zlength_sublist in R by lia.
  unfold is_ace in HA. rewrite Zlength_label_of in HA.
  destruct (4 <=? index_of 46 (sublist st (Zlength s) s)) eqn:E; [|discriminate].
  apply Z.leb_le in E. split; [lia|]. split; [lia|].
  unfold ace_in. rewrite sublist_sublist by lia.
  rewrite sublist_app1 by lia. f_equal; lia.
Qed.

(* The two outcomes of the decoding of the A-label at st into the buffer bv (512 code points). *)
Lemma ace_dec_cases: forall s st cap w sh bv,
  str_ok s -> 0 <= st <= Zlength s -> is_ace (label_of (rest_at s st)) = true -> Zlength bv = 512 ->
  (exists arr, decode_result (ace_in (rest_at s st)) 512 bv = (0, arr, 512) /\ Zlength arr = 512 /\
     label_step cap (w, sh) (label_of (rest_at s st)) = (false, (w, sh))) \/
  (exists cps, decode_result (ace_in (rest_at s st)) 512 bv =
       (1, vb cps ++ sublist (Zlength cps) 512 bv, Zlength cps) /\ cps_ok cps bv /\
     label_step cap (w, sh) (label_of (rest_at s st)) = put_utf8s cap (w, sh) cps).
Proof.
  intros s st cap w sh bv OK Hst HA HB.
  destruct (ace_idx s st Hst HA) as [J1 [J2 _]].
  assert (OKi: bytes_ok (ace_in (rest_at s st))).
  { unfold ace_in, rest_at. apply Forall_sublist, Forall_sublist.
    eapply Forall_impl; [|exact OK]. simpl; intros; lia. }
  assert (LS: label_step cap (w, sh) (label_of (rest_at s st)) =
    if maxint <=? Zlength (ace_in (rest_at s st)) then (false, (w, sh)) else
    match decode (ace_in (rest_at s st)) 512 with
    | (true, cps) => put_utf8s cap (w, sh) cps
    | (false, _) => (false, (w, sh))
    end).
  { unfold label_step. rewrite HA. rewrite Zlength_label_of.
    unfold label_of, ace_in. rewrite sublist_sublist by lia. rewrite !Z.add_0_r. reflexivity. }
  rewrite LS. unfold decode_result.
  change Int.max_unsigned with maxint.
  destruct (maxint <=? Zlength (ace_in (rest_at s st))).
  { left. exists bv. auto. }
  destruct (ace_out_range (ace_in (rest_at s st)) 512 OKi ltac:(lia)) as [F L].
  destruct (decode (ace_in (rest_at s st)) 512) as [ok out]. simpl in F, L.
  destruct ok.
  - right. exists out. split; [reflexivity|]. split; [|reflexivity]. split; auto.
  - left. exists (vb out ++ sublist (Zlength out) 512 bv). split; [reflexivity|]. split; [|reflexivity].
    rewrite Zlength_app, Zlength_vb, Zlength_sublist by (pose proof (Zlength_nonneg out); lia). lia.
Qed.
