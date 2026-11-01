(* The first piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): the draws of len, label, cps, outlen,
   out, its copy saved and want, up to the NULL test. *)
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

Local Notation CCS := OpensslPunycode.proof.laws.common.HelperSpec.CS.

(* A block of n octets from any_bytes or copy_of (at the helpers' compspecs) as the btok/bdat pair of the cuts. *)
Lemma ru8_split_bytes n v p:
  (if eq_dec p nullval then emp
   else @malloc_token CCS Ews (tarray tuchar n) p * @data_at CCS Ews (tarray tuchar n) v p)
  |-- btok (tarray tuchar n) p * bdat (tarray tuchar n) v p.
Proof.
  unfold btok, bdat. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  rewrite (data_at_tuchar_cs CCS CS).
  rewrite (@malloc_token_change_composite CCS CS (CCE_any CCS CS) Ews (tarray tuchar n)) by reflexivity.
  auto.
Qed.

(* A block of type t from malloc as the btok/bdat pair, its contents undefined. *)
Lemma ru8_split_malloc t p:
  (if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p)
  |-- btok t p * bdat t (default_val t) p.
Proof.
  unfold btok, bdat. destruct (eq_dec p nullval); [ rewrite emp_sepcon; auto | ].
  rewrite data_at__eq; auto.
Qed.

Lemma piece0 : piece7_stmt -> piece0_stmt.
Proof.
  intros HK Espec gv vc. unfold pre0, T0, ret0, main_post, Delta_main. abbreviate_semax.
  (* len = upto(PTRDIFF_MAX - 5) *)
  forward_call (Int64.max_signed - 5).
  Intros len.
  (* label = any_bytes(len + 5) *)
  forward_call (len + 5, gv).
  Intros vret. destruct vret as [pl lbs]. simpl fst in *. simpl snd in *.
  Intros.
  sep_apply (ru8_split_bytes (len + 5) (vb lbs) pl). Intros.
  (* cps = malloc(512 * sizeof(unsigned int)) *)
  forward_call (tarray tuint 512, gv).
  { simpl; rep_lia. }
  Intros pc.
  sep_apply (ru8_split_malloc (tarray tuint 512) pc). Intros.
  (* outlen = upto(PTRDIFF_MAX); out = any_bytes(outlen); saved = copy_of(out, outlen) *)
  forward_call (Int64.max_signed).
  Intros outlen.
  forward_call (outlen, gv).
  Intros vret. destruct vret as [pout ob]. simpl fst in *. simpl snd in *.
  Intros. subst outlen.
  forward_call (Ews, pout, ob, Zlength ob, gv).
  Intros psaved. rewrite sublist_same by lia.
  sep_apply (ru8_split_bytes (Zlength ob) (vb ob) pout). Intros.
  sep_apply (ru8_split_bytes (Zlength ob) (vb ob) psaved). Intros.
  (* want = malloc(4 * 512 + 1) *)
  forward_call (tarray tuchar 2049, gv).
  { simpl; rep_lia. }
  Intros pw.
  sep_apply (ru8_split_malloc (tarray tuchar 2049) pw). Intros.
  eapply semax_pre; [ | apply (HK Espec gv vc len lbs pl pc (Zlength ob) ob pout psaved pw) ].
  unfold pre7.
  change (default_val (tarray tuint 512)) with (Zrepeat Vundef 512).
  change (default_val (tarray tuchar 2049)) with (Zrepeat Vundef 2049).
  entailer!.
Qed.
