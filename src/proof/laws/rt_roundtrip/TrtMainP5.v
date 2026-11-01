(* Piece 5 of the main of harness/rt_roundtrip.c: the test
   `cps == NULL || out == NULL || encoding == NULL || !encode(cps, m, encoding, room, &len) || len >= 0xFFFFFFFF`
   and its return (TrtMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtMainDefs.
Local Open Scope logic.

(* The test p == NULL of a block that may be NULL is defined. *)
Lemma trt_block_tc_test {cs: compspecs} t n v q P:
  (0 < n -> sizeof (tarray t n) > 0) -> sizeof (tarray t 0) <= 0 -> 0 <= n ->
  jtok t n q * jarr t n v q * P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Ht H0 Hn. unfold jtok, jarr. destruct (eq_dec q nullval).
  - subst. simpl. entailer!.
  - unfold arr0. destruct (Z.eq_dec n 0).
    + subst. sep_apply (malloc_token_valid_pointer Ews (tarray t 0) q). entailer!.
    + sep_apply (data_at_valid_ptr Ews (tarray t n) v q); [ apply readable_nonidentity; auto | apply Ht; lia | ].
      entailer!.
Qed.

(* The first octets of an array of octets, the others dropped. *)
Lemma trt_arr0_prefix {cs: compspecs} sh n (l rest: list val) q:
  0 <= Zlength l <= n -> Zlength rest = n - Zlength l ->
  arr0 sh tuchar n (l ++ rest) q |-- arr0 sh tuchar (Zlength l) l q * TT.
Proof.
  intros Hl Hr. unfold arr0.
  destruct (Z.eq_dec (Zlength l) 0); [ entailer! | ].
  destruct (Z.eq_dec n 0); [ lia | ].
  unfold tarray. rewrite (split2_data_at_Tarray_app (Zlength l) n sh tuchar l rest) by auto.
  cancel.
Qed.

Ltac nonnull_cmp q :=
  destruct q; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

Lemma piece5 : piece6_stmt -> piece5_stmt.
Proof.
  intros H6 Espec gv vl vc cps outs room pc po pe. unfold pre5, T5, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. pose proof (Zlength_nonneg cps).
  forward_if (temp _t'6 (Vint (Int.repr (if Val.eq pc nullval then 1 else if Val.eq po nullval then 1 else 0)))).
  { apply derives_trans with (@jtok C.CS tuint (Zlength cps) pc * @jarr C.CS tuint (Zlength cps) (vb cps) pc * TT)%logic;
      [ cancel | apply trt_block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
  { forward. entailer!. }
  { forward.
    { go_lower.
      apply derives_trans with (@jtok C.CS tuint (Zlength cps) po * @jarr C.CS tuint (Zlength cps) (vb outs) po * TT)%logic;
        [ cancel | apply trt_block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pc nullval); [ contradiction | ].
    destruct (Val.eq po nullval); [ subst; reflexivity | ].
    nonnull_cmp po. }
  forward_if (temp _t'7 (Vint (Int.repr (if Val.eq pc nullval then 1 else if Val.eq po nullval then 1 else
    if Val.eq pe nullval then 1 else 0)))).
  { forward. entailer!.
    destruct (Val.eq pc nullval); [ reflexivity | ]. destruct (Val.eq po nullval); [ reflexivity | ].
    contradiction. }
  { forward.
    { go_lower.
      apply derives_trans with (jtok tuchar room pe * jarr tuchar room (Zrepeat Vundef room) pe * TT)%logic;
        [ cancel | apply trt_block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    entailer!. destruct (Val.eq pc nullval); [ discriminate | ].
    destruct (Val.eq po nullval); [ discriminate | ].
    destruct (Val.eq pe nullval); [ subst; reflexivity | ].
    nonnull_cmp pe. }
  assert (Ht7: (if Val.eq pc nullval then 1 else if Val.eq po nullval then 1 else
    if Val.eq pe nullval then 1 else 0) = 1 \/ (pc <> nullval /\ po <> nullval /\ pe <> nullval /\
    (if Val.eq pc nullval then 1 else if Val.eq po nullval then 1 else if Val.eq pe nullval then 1 else 0) = 0)).
  { destruct (Val.eq pc nullval); auto. destruct (Val.eq po nullval); auto. destruct (Val.eq pe nullval); auto. }
  destruct Ht7 as [E | [Hpc [Hpo [Hpe E]]]]; rewrite E; clear E.
  - (* a NULL block: return 0 *)
    forward_if (temp _t'8 (Vint Int.one)).
    { forward. entailer!. }
    { first [ discriminate | congruence ]. }
    forward_if (temp _t'10 (Vint Int.one)).
    { forward. entailer!. }
    { first [ discriminate | congruence ]. }
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. Exists (Int.repr 0). entailer!. }
    { first [ discriminate | congruence ]. }
  - (* three blocks: the call of encode *)
    unfold jtok, jarr. rewrite !if_false by assumption.
    forward_if (EX o': list val,
      PROP (Zlength o' = room)
      LOCAL (temp _t'8 (Vint (Int.repr (if RefRt.encode_fits cps room then 0 else 1)));
             temp _encoding pe; temp _out po; temp _cps pc;
             temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _len tulong vl; lvar _count tuint vc)
      SEP (@malloc_token C.CS Ews (tarray tuint (Zlength cps)) pc;
           @arr0 C.CS Ews tuint (Zlength cps) (vb cps) pc;
           @malloc_token C.CS Ews (tarray tuint (Zlength cps)) po;
           @arr0 C.CS Ews tuint (Zlength cps) (vb outs) po;
           malloc_token Ews (tarray tuchar room) pe;
           arr0 Ews tuchar room (RefRt.encode_out cps room (Zrepeat Vundef room) o') pe;
           if RefRt.encode_fits cps room then data_at Tsh tulong (Vlong (Int64.repr (RefRt.encode_len cps))) vl
           else data_at_ Tsh tulong vl;
           data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
    { first [ discriminate | congruence ]. }
    { rewrite (arr0_tuint_cs C.CS CS _ _ _ pc).
      forward_call (Ews, pc, cps, Ews, pe, room, Zrepeat Vundef room, Tsh, vl).
      { rewrite Zlength_Zrepeat; lia. }
      Intros o'.
      forward.
      Exists o'. rewrite (arr0_tuint_cs C.CS CS _ _ _ pc).
      entailer!. destruct (RefRt.encode_fits _ _); reflexivity. }
    Intros o'.
    destruct (RefRt.encode_fits cps room) eqn:Ef.
    + (* encode succeeded *)
      unfold RefRt.encode_fits in Ef. unfold RefRt.encode_out, RefRt.encode_len.
      destruct (encode cps) as [e|] eqn:He; [ | discriminate ].
      rewrite Ef. apply Z.leb_le in Ef.
      forward_if (temp _t'10 (Vint (Int.repr (if Z.leb Int.max_unsigned (Zlength e) then 1 else 0)))).
      { first [ discriminate | congruence ]. }
      { forward. forward. entailer!.
        change (Int.unsigned (Int.repr (-1))) with 4294967295. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (zlt (Zlength e) 4294967295), (Z.leb_spec Int.max_unsigned (Zlength e)); simpl;
          reflexivity || rep_lia. }
      forward_if (PROP (Zlength e < Int.max_unsigned)
        LOCAL (temp _encoding pe; temp _out po; temp _cps pc;
               temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _len tulong vl; lvar _count tuint vc)
        SEP (@malloc_token C.CS Ews (tarray tuint (Zlength cps)) pc;
             @arr0 C.CS Ews tuint (Zlength cps) (vb cps) pc;
             @malloc_token C.CS Ews (tarray tuint (Zlength cps)) po;
             @arr0 C.CS Ews tuint (Zlength cps) (vb outs) po;
             malloc_token Ews (tarray tuchar room) pe;
             arr0 Ews tuchar room (vb e ++ sublist (Zlength e) room (Zrepeat Vundef room)) pe;
             data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) vl;
             data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
      { forward. Exists (Int.repr 0). entailer!. }
      { forward. entailer!. destruct (Z.leb_spec Int.max_unsigned (Zlength e)); [ discriminate | lia ]. }
      Intros.
      sep_apply (trt_arr0_prefix Ews room (vb e) (sublist (Zlength e) room (Zrepeat Vundef room)) pe);
        [ rewrite Zlength_vb; pose proof (Zlength_nonneg e); lia
        | rewrite Zlength_vb; list_solve | ]. Intros.
      rewrite Zlength_vb.
      eapply semax_pre; [ | apply (H6 Espec gv vl vc cps outs e pc po pe) ].
      unfold pre6. rewrite !(arr0_tuint_cs C.CS CS). entailer!.
    + (* encode failed: return 0 *)
      forward_if (temp _t'10 (Vint Int.one)).
      { forward. entailer!. }
      { first [ discriminate | congruence ]. }
      forward_if (PROP (False) LOCAL () SEP ()).
      { forward. Exists (Int.repr 0). entailer!. }
      { first [ discriminate | congruence ]. }
Qed.
