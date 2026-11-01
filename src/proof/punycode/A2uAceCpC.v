(* ossl_a2ulabel, ACE branch, code-point loop body, parts C and D: t'8 = WPACKET_memcpy(&pkt, seed, utfsize);
   if (!t'8) result = 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uAceRange.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.proof.punycode.A2uAceDefs.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.

Lemma cpc_utf8_len: forall c, Zlength (utf8 c) <= 4.
Proof.
  intros. unfold utf8.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma cpc_utf8_bytes: forall c, 0 <= c -> bytes_ok (utf8 c).
Proof.
  intros. unfold utf8, bytes_ok. change Byte.max_unsigned with 255.
  assert (0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (0 <= (c / 64) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (0 <= (c / 4096) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  destruct (c <? 128) eqn:E1; [apply Z.ltb_lt in E1; repeat first [apply Forall_nil | apply Forall_cons; [lia|]]|apply Z.ltb_ge in E1].
  destruct (c <? 2048) eqn:E2; [apply Z.ltb_lt in E2|apply Z.ltb_ge in E2].
  { assert (0 <= c / 64 < 32) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    repeat first [apply Forall_nil | apply Forall_cons; [lia|]]. }
  destruct (c <? 65536) eqn:E3; [apply Z.ltb_lt in E3|apply Z.ltb_ge in E3].
  { assert (0 <= c / 4096 < 16) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    repeat first [apply Forall_nil | apply Forall_cons; [lia|]]. }
  destruct (c <=? 1114111) eqn:E4; [apply Z.leb_le in E4|constructor].
  assert (0 <= c / 262144 < 5) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  repeat first [apply Forall_nil | apply Forall_cons; [lia|]].
Qed.
Lemma cp_cd_ok: forall (Espec: OracleKind) gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh R,
  a2u_ctx shi pin s sho out cap init -> cps_ok cps bv ->
  semax DeltaA
    (cp_b gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i w sh)
    (Ssequence s_cpc s_cpd)
    (overridePost (cp_mid gv shi pin s sho out cap init tk zf live sub vbuf vpkt vbs vseed st w0 sh0 cps bv i) R).
Proof.
  intros. unfold cp_b, cp_a, s_cpc, s_cpd. abbreviate_semax.
  destruct H as (Hshi & Hsho & Hstr & Hpin & Hfc & Hcap & Hinit & Hout).
  destruct H0 as (HF & Hn & Hbv).
  Intros new. apply semax_extract_prop; intros HL0. Intros.
  assert (Hc: 0 <= Znth i cps <= maxint) by (rewrite Forall_Znth in HF; apply HF; lia).
  pose proof (cpc_utf8_len (Znth i cps)) as HL4.
  pose proof (cpc_utf8_bytes (Znth i cps) (proj1 Hc)) as HB.
  set (l := utf8 (Znth i cps)) in *.
  assert_PROP (isptr vseed) as Hvs by entailer!.
  rewrite (split2_data_at_Tarray_tuchar Tsh 6 (Zlength l) new vseed) by lia.
  rewrite H2.
  assert (PL: forall cs: compspecs, @data_at CS Tsh (Tarray tuchar (Zlength l) noattr) (vb l) vseed =
                                     @arr0 cs Tsh tuchar (Zlength l) (vb l) vseed).
  { intros. change (Tarray tuchar (Zlength l) noattr) with (tarray tuchar (Zlength l)). rewrite (data_at_tuchar_cs CS cs). apply data_at_arr0; auto. intros; lia. }
  rewrite (PL PkCS). Intros.
  forward_call (Tsh, vpkt, sho, out, cap, init, w, sub, Tsh, vseed, l).
  rewrite <- (PL CS).
  assert (HM: put_utf8s cap (w0, sh0) cps =
    put_utf8s cap (fst (put cap (w, false) l), orb sh (negb (PacketSpec.put_ok cap w l))) (sublist (i + 1) (Zlength cps) cps)).
  { rewrite H0, put_utf8s_next by lia. fold l.
    replace (Zlength l =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite put_split. reflexivity. }
  destruct (PacketSpec.put_ok cap w l) eqn:EP; [rewrite orb_false_r in HM | rewrite orb_true_r in HM];
  forward_if.
  1,4: (exfalso; first [discriminate | apply H3; reflexivity]).
  all: try forward.
  all: destruct R; cbv beta iota; cbn [tycontext.RA_normal].
  - Exists (fst (put cap (w, false) l)) sh. Exists new.
    rewrite (split2_data_at_Tarray_tuchar Tsh 6 (Zlength l) new vseed) by lia. rewrite H2.
    entailer!.
  - Exists (fst (put cap (w, false) l)) true. Exists new.
    rewrite (split2_data_at_Tarray_tuchar Tsh 6 (Zlength l) new vseed) by lia. rewrite H2.
    entailer!.
Qed.
