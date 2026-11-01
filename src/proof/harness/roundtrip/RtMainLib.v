(* Small lemmas for the pieces of the main of harness/x_roundtrip.c: scalars and arrays of scalars do not depend on
   the compspecs. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.

Section Cs.
Context (cs1 cs2: compspecs).

Lemma data_at_cs_tint: forall sh v p, @data_at cs1 sh tint v p = @data_at cs2 sh tint v p.
Proof. intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity]. Qed.

Lemma data_at_cs_tuint: forall sh v p, @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof. intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity]. Qed.

Lemma data_at_cs_tlong: forall sh v p, @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof. intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity]. Qed.

Lemma data_at_cs_tschar: forall sh v p, @data_at cs1 sh tschar v p = @data_at cs2 sh tschar v p.
Proof. intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity]. Qed.

Lemma data_at_cs_tarray_tschar: forall sh n v p,
  @data_at cs1 sh (tarray tschar n) v p = @data_at cs2 sh (tarray tschar n) v p.
Proof. intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [apply JMeq_refl | reflexivity]. Qed.
End Cs.

(* A one-octet global seen as unsigned char is the same octet seen as char (values below 128). *)
Lemma data_at_tuchar_tschar_1 {cs: compspecs}: forall sh (b: Z) p,
  0 <= b < 128 ->
  data_at sh tuchar (Vint (Int.repr b)) p = data_at sh tschar (Vint (Int.repr b)) p.
Proof.
  intros sh b p Hb.
  rewrite <- (data_at_tuchar_singleton_array_eq sh), <- (data_at_tschar_singleton_array_eq sh).
  assert (E1: [Vint (Int.repr b)] = map Vubyte [Byte.repr b]).
  { simpl. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity. }
  assert (E2: [Vint (Int.repr b)] = map Vbyte [Byte.repr b]).
  { simpl. unfold Vbyte. rewrite Byte.signed_repr by rep_lia. reflexivity. }
  rewrite E1 at 1. rewrite E2. symmetry. apply data_at_tarray_tschar_tuchar.
Qed.
