(* Piece 0 of the main of harness/api_a2ulabel_labels.c, the state after its ten draws (statement 10 of AlbMainDefs):
   the blocks any_bytes and malloc give (each NULL or allocated), kept folded, the tactics of the || chain of NULL
   tests, and two cuts: before statement 10 (the NULL test, AlbP0Null.v) and before statement 11 (the test of the
   sizes, AlbP0Size.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbMainDefs.
Local Open Scope logic.

Module H := OpensslPunycode.proof.laws.common.HelperSpec.

(* A block from any_bytes: NULL, or its malloc token and its octets.  Kept folded in the main: VST's automation is
   slow on the conditional of the unfolded form. *)
Definition ablk (n: Z) (v: list val) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else @malloc_token H.CS Ews (tarray tuchar n) p * @data_at H.CS Ews (tarray tuchar n) v p.

(* The test p == NULL of such a block is defined. *)
Lemma ablk_tc_test n v p P: 0 <= n ->
  ablk n v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hn. unfold ablk. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - sep_apply (@data_at_data_at_ H.CS Ews (tarray tuchar n) v p).
    eapply derives_trans; [ | apply (@CmnLib.cmn_malloc_tc_test0 H.CS (tarray tuchar n) p P) ].
    + rewrite if_false by auto. cancel.
    + simpl. rep_lia.
Qed.

(* p is NULL, as a boolean: the || chain of NULL tests computes the disjunction of these. *)
Definition isnull (p: val) : bool := if Val.eq p nullval then true else false.

Ltac nonnull_cmp p :=
  destruct p; try contradiction; try reflexivity;
  match goal with H: is_pointer_or_null (Vlong ?i) |- _ => simpl in H; subst i end;
  match goal with H: Vlong _ <> nullval |- _ => exfalso; apply H; reflexivity end.

(* Closes the value of one test of the || chain (the earlier tests' disjunction B, then the test of p): when B
   holds the value is 1; otherwise it is the value of p == NULL.  Only B is split, not each of its tests. *)
Ltac or_then :=
  match goal with Hb: (if ?B then 1 else 0) <> 0 |- _ =>
    destruct B; [ reflexivity | exfalso; apply Hb; reflexivity ] end.
Ltac or_else p :=
  match goal with Hb: Int.repr (if ?B then 1 else 0) = Int.zero |- _ =>
    destruct B; [ inversion Hb
                | simpl orb; unfold isnull; destruct (Val.eq p nullval); [ subst; reflexivity | nonnull_cmp p ] ] end.

Lemma int_flag_false (b: bool): Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. destruct b; [ intros Hb; inversion Hb | auto ]. Qed.

(* Past the chain with value 0: no block is NULL. *)
Ltac all_nonnull :=
  match goal with Hb: Int.repr (if _ then 1 else 0) = Int.zero |- _ =>
    apply int_flag_false in Hb; rewrite !Bool.orb_false_iff in Hb; unfold isnull in Hb end;
  repeat match goal with Hx: _ /\ _ |- _ => destruct Hx end;
  repeat match goal with Hx: (if Val.eq ?q nullval then true else false) = false |- _ =>
    destruct (Val.eq q nullval); [ discriminate Hx | clear Hx ] end;
  repeat split; assumption.

(* The block malloc gives name: NULL, or its token and its uninitialized octets. *)
Definition nblk (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p.

(* The cut after the ten draws: statement 10 (the NULL test) on. *)
Definition T10 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 10 main_big.

Definition pre10 (gv: globals) (len1 len2: Z) (bs1 bs2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z)
    (ps1 ps2 pn po1 po2 po: val) : environ -> mpred :=
  PROP (0 <= len1 <= Int64.max_signed - 2; 0 <= len2 <= Int64.max_signed - 2 - len1;
        Zlength bs1 = (len1 + 1)%Z; bytes_ok bs1; Zlength bs2 = (len2 + 1)%Z; bytes_ok bs2;
        0 <= outlen1 <= Int64.max_signed; 0 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob)
  LOCAL (temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
         temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
  SEP (mem_mgr gv; ablk (outlen1 + outlen2) (vb ob) po; ablk outlen2 (vb ob2) po2; ablk outlen1 (vb ob1) po1;
       nblk (len1 + len2 + 2) pn; ablk (len2 + 1) (vb bs2) ps2; ablk (len1 + 1) (vb bs1) ps1;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; TT).

Definition null_stmt : Prop := forall (Espec: OracleKind) gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob
    ps1 ps2 pn po1 po2 po,
  semax Delta_main (pre10 gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po)
    (Ssequence T10 ret0) main_post.

(* The cut after the NULL test: statement 11 (the test of the sizes) on; no block is NULL. *)
Definition T11 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 11 main_big.

Definition pre11 (gv: globals) (len1 len2: Z) (bs1 bs2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z)
    (ps1 ps2 pn po1 po2 po: val) : environ -> mpred :=
  PROP (0 <= len1 <= Int64.max_signed - 2; 0 <= len2 <= Int64.max_signed - 2 - len1;
        Zlength bs1 = (len1 + 1)%Z; bytes_ok bs1; Zlength bs2 = (len2 + 1)%Z; bytes_ok bs2;
        0 <= outlen1 <= Int64.max_signed; 0 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob;
        ps1 <> nullval; ps2 <> nullval; pn <> nullval; po1 <> nullval; po2 <> nullval; po <> nullval)
  LOCAL (temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
         temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
  SEP (mem_mgr gv; ablk (outlen1 + outlen2) (vb ob) po; ablk outlen2 (vb ob2) po2; ablk outlen1 (vb ob1) po1;
       nblk (len1 + len2 + 2) pn; ablk (len2 + 1) (vb bs2) ps2; ablk (len1 + 1) (vb bs1) ps1;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; TT).

Definition size_stmt : Prop := forall (Espec: OracleKind) gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob
    ps1 ps2 pn po1 po2 po,
  semax Delta_main (pre11 gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po)
    (Ssequence T11 ret0) main_post.
