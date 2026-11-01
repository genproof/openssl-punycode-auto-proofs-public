(* A piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): the NULL test of the five blocks and of outlen,
   and the octets "xn--" and the NUL written into label. *)
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

Local Open Scope logic.

(* The test q == NULL of a block of type t from malloc is defined: the token is a valid pointer when t has size 0,
   the contents when it is larger. *)
Lemma btok_tc_test t v q P:
  0 <= sizeof t -> btok t q * bdat t v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold btok, bdat. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - destruct (Z.eq_dec (sizeof t) 0).
    + sep_apply (malloc_token_valid_pointer Ews t q); [ lia | ]. entailer!.
    + sep_apply (data_at_valid_ptr Ews t v q); [ apply readable_nonidentity; auto | lia | ]. entailer!.
Qed.

(* The joins of the || chain: the temp just set is the value the post wants; the rest of the state is unchanged.
   Cheaper than entailer! on this large state. *)
Ltac join_temp :=
  match goal with |- ENTAIL _, PROPx _ (LOCALx (temp ?i ?x :: _) _) |-- PROPx _ (LOCALx (temp ?i ?y :: _) _) =>
    replace x with y; [ apply ENTAIL_refl | ] end.

(* The value equations of the joins: case on each pointer being NULL; a pointer that is not NULL compares unequal
   to NULL. *)
Ltac join_val Hptr :=
  let Ppl := fresh "P" in let Ppc := fresh "P" in let Ppout := fresh "P" in let Ppsaved := fresh "P" in
  let Ppw := fresh "P" in
  destruct Hptr as (Ppl & Ppc & Ppout & Ppsaved & Ppw);
  repeat match goal with |- context [Val.eq ?p nullval] => destruct (Val.eq p nullval) as [-> | ?] end;
  simpl in *; try contradiction; try reflexivity;
  try match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end;
  match goal with |- context [sem_cmp_pp _ ?p _] =>
    destruct p; try contradiction; [ simpl in *; subst; exfalso; auto | reflexivity ] end.

Lemma piece7 : piece13_stmt -> piece7_stmt.
Proof.
  intros HK Espec gv vc len lbs pl pc outlen ob pout psaved pw.
  unfold pre7, T7, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  assert_PROP (is_pointer_or_null pl /\ is_pointer_or_null pc /\ is_pointer_or_null pout /\
               is_pointer_or_null psaved /\ is_pointer_or_null pw) as Hptr.
  { go_lower. apply prop_right; tauto. }
  freeze FR := (data_at_ _ _ _) (mem_mgr _) (PunySpec.puny_consts _) (PunySpec.xn_lit _)
    (ShimSpec.shim_state _ _ _ _) TT.
  (* if (label == NULL || cps == NULL || out == NULL || saved == NULL || want == NULL || outlen == 0) return 0 *)
  forward_if (temp _t'8 (Vint (Int.repr (if Val.eq pl nullval then 1 else if Val.eq pc nullval then 1 else 0)))).
  { apply derives_trans with (btok (tarray tuchar (len + 5)) pl * bdat (tarray tuchar (len + 5)) (vb lbs) pl * TT);
      [ cancel | apply btok_tc_test; simpl; lia ]. }
  { forward. join_temp. join_val Hptr. }
  { forward.
    { go_lower.
      apply derives_trans with (btok (tarray tuint 512) pc * bdat (tarray tuint 512) (Zrepeat Vundef 512) pc * TT);
        [ cancel | apply btok_tc_test; simpl; lia ]. }
    join_temp. join_val Hptr. }
  forward_if (temp _t'9 (Vint (Int.repr (if Val.eq pl nullval then 1 else if Val.eq pc nullval then 1 else
    if Val.eq pout nullval then 1 else 0)))).
  { forward. join_temp. join_val Hptr. }
  { forward.
    { go_lower.
      apply derives_trans with (btok (tarray tuchar outlen) pout * bdat (tarray tuchar outlen) (vb ob) pout * TT);
        [ cancel | apply btok_tc_test; simpl; lia ]. }
    join_temp. join_val Hptr. }
  forward_if (temp _t'10 (Vint (Int.repr (if Val.eq pl nullval then 1 else if Val.eq pc nullval then 1 else
    if Val.eq pout nullval then 1 else if Val.eq psaved nullval then 1 else 0)))).
  { forward. join_temp. join_val Hptr. }
  { forward.
    { go_lower.
      apply derives_trans with (btok (tarray tuchar outlen) psaved * bdat (tarray tuchar outlen) (vb ob) psaved * TT);
        [ cancel | apply btok_tc_test; simpl; lia ]. }
    join_temp. join_val Hptr. }
  forward_if (temp _t'11 (Vint (Int.repr (if Val.eq pl nullval then 1 else if Val.eq pc nullval then 1 else
    if Val.eq pout nullval then 1 else if Val.eq psaved nullval then 1 else if Val.eq pw nullval then 1 else 0)))).
  { forward. join_temp. join_val Hptr. }
  { forward.
    { go_lower.
      apply derives_trans with (btok (tarray tuchar 2049) pw * bdat (tarray tuchar 2049) (Zrepeat Vundef 2049) pw * TT);
        [ cancel | apply btok_tc_test; simpl; lia ]. }
    join_temp. join_val Hptr. }
  forward_if (temp _t'12 (Vint (Int.repr (if Val.eq pl nullval then 1 else if Val.eq pc nullval then 1 else
    if Val.eq pout nullval then 1 else if Val.eq psaved nullval then 1 else if Val.eq pw nullval then 1 else
    if Z.eq_dec outlen 0 then 1 else 0)))).
  { forward. join_temp. join_val Hptr. }
  { forward. join_temp.
    match goal with H: Int.repr _ = Int.zero |- _ => revert H end.
    repeat match goal with |- context [Val.eq ?p nullval] => destruct (Val.eq p nullval) end;
      intro Hz; try (exfalso; exact (Int.one_not_zero Hz)).
    destruct (Z.eq_dec outlen 0) as [-> | Hn]; [ reflexivity | ].
    simpl. change (Int.signed (Int.repr 0)) with 0. rewrite Int64.eq_false; [ reflexivity | ].
    intro E; apply (f_equal Int64.unsigned) in E; rewrite !Int64.unsigned_repr in E by rep_lia; lia. }
  thaw FR.
  forward_if (PROP (pl <> nullval; pc <> nullval; pout <> nullval; psaved <> nullval; pw <> nullval; outlen <> 0)
    LOCAL (temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
           temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
    SEP (btok (tarray tuchar (len + 5)) pl; bdat (tarray tuchar (len + 5)) (vb lbs) pl;
         btok (tarray tuint 512) pc; bdat (tarray tuint 512) (Zrepeat Vundef 512) pc;
         btok (tarray tuchar outlen) pout; bdat (tarray tuchar outlen) (vb ob) pout;
         btok (tarray tuchar outlen) psaved; bdat (tarray tuchar outlen) (vb ob) psaved;
         btok (tarray tuchar 2049) pw; bdat (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
         data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
         OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
         TT)).
  { forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!.
    match goal with H: Int.repr _ = Int.zero |- _ => revert H end.
    repeat match goal with |- context [Val.eq ?p nullval] => destruct (Val.eq p nullval) end;
      destruct (Z.eq_dec (Zlength ob) 0); intro Hz; try (exfalso; exact (Int.one_not_zero Hz)); tauto. }
  Intros. unfold btok, bdat. rewrite !if_false by assumption.
  (* label[0..3] = "xn--"; label[len + 4] = 0 *)
  forward. forward. forward. forward. forward.
  set (s := sublist 4 (len + 4) lbs).
  match goal with |- context [data_at Ews (tarray tuchar (len + 5)) ?v pl] =>
    replace v with (vb (xn ++ s ++ [0])) end.
  2: { change (Int.zero_ext 8 (Int.repr 120)) with (Int.repr 120).
       change (Int.zero_ext 8 (Int.repr 110)) with (Int.repr 110).
       change (Int.zero_ext 8 (Int.repr 45)) with (Int.repr 45).
       change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
       unfold vb, xn. subst s. list_solve. }
  assert (Zlength s = len) by (subst s; list_solve).
  assert (bytes_ok s) by (subst s; apply Forall_sublist; auto).
  unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS; subst Delta POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (HK Espec gv vc len s pl pc outlen ob pout psaved pw) ].
  unfold pre13. entailer!.
Qed.
