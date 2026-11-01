(* The third piece of the main of harness/api_a2ulabel_copy.c, its inner part: one turn of the gp_assume loop at a
   position i that starts a label.  The tests `in[i] == 'x' || in[i] == 'X'`, `in[i + 1] == 'n' || ...`,
   `in[i + 2] == '-'`, `in[i + 3] == '-'` are computed as 0/1 values, and the gp_assume call excludes the label
   prefix "xn--" at i.  Also the facts about the loop's progress (acp_upto) used by AcpMainP9. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_copy.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpModel.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_copy.AcpMainDefs.

(* The octets of s at j, j + 1, j + 2, j + 3 are x/X, n/N, '-', '-': the label starting at j begins with "xn--". *)
Definition acp_pfx (s: list Z) (j: Z) : Prop :=
  (Znth j s = 120 \/ Znth j s = 88) /\ (Znth (j + 1) s = 110 \/ Znth (j + 1) s = 78) /\
  Znth (j + 2) s = 45 /\ Znth (j + 3) s = 45.

(* What the loop has established after its first i turns: no label starting before i begins with "xn--". *)
Definition acp_upto (s: list Z) (i: Z) : Prop :=
  forall j, 0 <= j < i -> j + 3 < Zlength s -> (j = 0 \/ Znth (j - 1) s = 46) -> ~ acp_pfx s j.

Lemma acp_upto_0 s: acp_upto s 0.
Proof. intros j Hj. lia. Qed.

Lemma acp_upto_noprefix s i: acp_upto s i -> Zlength s <= i + 3 -> acp_noprefix s.
Proof. intros H Hi j Hj Hj3 Hl. apply (H j); [ lia | exact Hj3 | exact Hl ]. Qed.

Lemma acp_upto_skip s i: acp_upto s i -> ~ (i = 0 \/ Znth (i - 1) s = 46) -> acp_upto s (i + 1).
Proof.
  intros H Hn j Hj Hj3 Hl. destruct (Z.eq_dec j i) as [-> | ]; [ contradiction | apply H; auto; lia ].
Qed.

Lemma acp_upto_step s i: acp_upto s i -> ~ acp_pfx s i -> acp_upto s (i + 1).
Proof.
  intros H Hn j Hj Hj3 Hl. destruct (Z.eq_dec j i) as [-> | ]; [ exact Hn | apply H; auto; lia ].
Qed.

(* The octet at a position of the string, read from the buffer s, NUL, t. *)
Lemma acp_znth s t i: 0 <= i < Zlength s -> Znth i (vb (s ++ [0] ++ t)) = Vint (Int.repr (Znth i s)).
Proof.
  intros. unfold vb. rewrite Znth_map by (rewrite !Zlength_app; list_solve). rewrite app_Znth1 by lia. reflexivity.
Qed.

(* The octets of the string are in 1 .. 255. *)
Lemma acp_byte s k: ShimSpec.str_ok s -> 0 <= k < Zlength s -> 1 <= Znth k s <= 255.
Proof. intros H Hk. unfold ShimSpec.str_ok in H. rewrite Forall_Znth in H. apply (H k Hk). Qed.

(* The value of the C test `b == c` on two octets. *)
Lemma acp_eqb b c: 0 <= b <= 255 -> 0 <= c <= 255 ->
  bool2val (Int.eq (Int.repr b) (Int.repr c)) = Vint (Int.repr (if b =? c then 1 else 0)).
Proof.
  intros Hb Hc. destruct (Z.eqb_spec b c) as [-> | Hn]; [ rewrite Int.eq_true; reflexivity | ].
  rewrite Int.eq_false; [ reflexivity | ]. intro E. apply repr_inj_unsigned in E; [ contradiction | rep_lia | rep_lia ].
Qed.

(* The same value, as entailer! leaves it. *)
Lemma acp_zeq b c: bool2val (zeq b c) = Vint (Int.repr (if b =? c then 1 else 0)).
Proof. destruct (zeq b c), (Z.eqb_spec b c); simpl; try lia; reflexivity. Qed.

(* The value of a C condition computed as 1 or 0 from a boolean. *)
Lemma acp_bit1 (b: bool): (if b then 1 else 0) <> 0 -> b = true.
Proof. destruct b; [ reflexivity | contradiction ]. Qed.

Lemma acp_bit0 (b: bool): Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. destruct b; [ discriminate | reflexivity ]. Qed.

Ltac acp_bits :=
  repeat match goal with
  | Hb: (if ?b then 1 else 0) <> 0 |- _ => apply acp_bit1 in Hb; try rewrite Hb
  | Hb: Int.repr (if ?b then 1 else 0) = Int.zero |- _ => apply acp_bit0 in Hb; try rewrite Hb
  end.

Ltac acp_cmp := first [ rewrite acp_zeq | rewrite acp_eqb by lia ].

(* Rewrites every load of the buffer at a position inside the string to the octet of s (the Znth of a load carries
   the Inhabitant of the reptype: normalize it first). *)
Ltac acp_rd :=
  repeat match goal with |- context [@Znth ?A ?d ?k (vb (?s ++ [0] ++ ?t))] =>
    change (@Znth A d k (vb (s ++ [0] ++ t))) with (Znth k (vb (s ++ [0] ++ t)));
    rewrite (acp_znth s t k) by lia
  | |- context [@Znth ?A ?d ?k (vb (?s ++ 0 :: ?t))] =>
    change (@Znth A d k (vb (s ++ 0 :: t))) with (Znth k (vb (s ++ [0] ++ t)));
    rewrite (acp_znth s t k) by lia end.

(* The statement run when the position i starts a label: the && / || chain and the gp_assume call. *)
Definition acp_chk : statement :=
  ltac:(let x := eval cbv [T9] in T9 in
        lazymatch x with Ssequence (Ssequence _ (Sloop (Ssequence _ (Ssequence _ (Sifthenelse _ ?b _))) _)) _ =>
          exact b end).

(* One turn of the loop at a label start i: afterwards the label at i does not begin with "xn--" either. *)
Lemma acp_check {Espec: OracleKind} gv len s t pin outlen ob pout psaved i v:
  ShimSpec.str_ok s -> (Zlength s + Zlength t)%Z = len -> 0 <= len < Int64.max_signed ->
  0 <= i -> i + 3 < Zlength s -> acp_upto s i ->
  semax Delta_main
    (PROP ()
     LOCAL (temp _t'13 v; temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr (Zlength s)));
            temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
     SEP (mem_mgr gv; PunySpec.puny_consts gv; PunySpec.xn_lit gv; ShimSpec.shim_state gv 0 0 0;
          data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
          data_at Ews (tarray tuchar outlen) (vb ob) pout;
          data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))
    acp_chk
    (normal_ret_assert
      (EX i: Z,
       PROP (0 <= i; i + 3 < Zlength s; acp_upto s (i + 1))
       LOCAL (temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr (Zlength s))); temp _saved psaved;
              temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
       SEP (mem_mgr gv; PunySpec.puny_consts gv; PunySpec.xn_lit gv; ShimSpec.shim_state gv 0 0 0;
            data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
            data_at Ews (tarray tuchar outlen) (vb ob) pout;
            data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT))).
Proof.
  intros H1 H3 H0 Hi0 Hi3 H8. unfold acp_chk, Delta_main. abbreviate_semax.
  pose proof (Zlength_nonneg s); pose proof (Zlength_nonneg t).
  pose proof (acp_byte s i H1 ltac:(lia)) as B0; pose proof (acp_byte s (i + 1) H1 ltac:(lia)) as B1;
  pose proof (acp_byte s (i + 2) H1 ltac:(lia)) as B2; pose proof (acp_byte s (i + 3) H1 ltac:(lia)) as B3.
  set (bx := orb (Znth i s =? 120) (Znth i s =? 88)).
  set (bn := orb (Znth (i + 1) s =? 110) (Znth (i + 1) s =? 78)).
  set (b2 := Znth (i + 2) s =? 45).
  set (b3 := Znth (i + 3) s =? 45).
  forward.
  { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  acp_rd.
  forward_if (temp _t'9 (Vint (Int.repr (if bx then 1 else 0)))).
  { forward. entailer!. match goal with E: Znth i s = 120 |- _ => unfold bx; rewrite E; reflexivity end. }
  { forward.
    { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    acp_rd. forward. entailer!. acp_cmp. unfold bx. replace (Znth i s =? 120) with false by lia.
    reflexivity. }
  forward_if (temp _t'10 (Vint (Int.repr (if andb bx bn then 1 else 0)))).
  { forward.
    { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    acp_rd.
    forward_if (temp _t'10 (Vint (Int.repr (if bn then 1 else 0)))).
    { forward. entailer!. match goal with E: Znth (i + 1) s = 110 |- _ => unfold bn; rewrite E; reflexivity end. }
    { forward.
      { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      acp_rd. forward. forward. entailer!. acp_cmp. unfold bn.
      replace (Znth (i + 1) s =? 110) with false by lia. destruct (Znth (i + 1) s =? 78); reflexivity. }
    entailer!. acp_bits. reflexivity. }
  { forward. entailer!. acp_bits. reflexivity. }
  forward_if (temp _t'11 (Vint (Int.repr (if andb (andb bx bn) b2 then 1 else 0)))).
  { forward.
    { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    acp_rd. forward. entailer!. acp_cmp. acp_bits. reflexivity. }
  { forward. entailer!. acp_bits. reflexivity. }
  forward_if (temp _t'12 (Vint (Int.repr (if andb (andb (andb bx bn) b2) b3 then 1 else 0)))).
  { forward.
    { entailer!. acp_rd. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    acp_rd. forward. entailer!. acp_cmp. acp_bits. reflexivity. }
  { forward. entailer!. acp_bits. reflexivity. }
  forward_call (Int.repr (if andb (andb (andb bx bn) b2) b3 then 0 else 1)).
  { entailer!. destruct (bx && bn && b2 && b3)%bool; reflexivity. }
  assert (Hn: ~ acp_pfx s i).
  { intros [P0 [P1 [P2 P3]]].
    assert (E: (bx && bn && b2 && b3)%bool = true)
      by (unfold bx, bn, b2, b3; destruct P0 as [-> | ->]; destruct P1 as [-> | ->]; rewrite P2, P3; reflexivity).
    match goal with Hc: Int.repr (if _ then 0 else 1) <> Int.zero |- _ => rewrite E in Hc; contradiction end. }
  Exists i. entailer!. apply acp_upto_step; auto.
Qed.
