(* A piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): the loop that writes the UTF-8 forms of the
   decoded code points into want (utf8), then want[size] = 0 and size++. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Lib.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Loop.

Lemma piece17 : piece20_stmt -> piece17_stmt.
Proof.
  intros Hnext Espec gv vc len s pl pc outlen ob pout psaved pw.
  unfold pre17. assert_PROP (bytes_ok s) as Hb by entailer!.
  destruct (ru8p17_cases s Hb) as [[Hv [Hc [Hz Hn]]] | [out [Hd [Hlo [Hr Hw]]]]].
  - (* no decoding: valid = 0 *)
    unfold dres. rewrite Hv, Hc.
    apply (ru8p17_loop gv vc len s pl pc outlen ob pout psaved pw false
             (snd (fst (OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512)))) 512 []);
      auto; try lia; discriminate.
  - (* the code points out *)
    unfold dres. rewrite Hd. simpl.
    pose proof (Zlength_nonneg out).
    apply (ru8p17_loop gv vc len s pl pc outlen ob pout psaved pw true
             (vb out ++ sublist (Zlength out) 512 (Zrepeat Vundef 512)) (Zlength out) out); auto; try lia.
    + unfold vb. rewrite Zlength_app, Zlength_map, Zlength_sublist; rewrite ?Zlength_Zrepeat; lia.
    + intros _. split; [reflexivity|]. split; [|auto].
      rewrite sublist_app1 by (rewrite ?Zlength_vb; lia). rewrite <- (Zlength_vb out). apply sublist_same; auto.
Qed.
