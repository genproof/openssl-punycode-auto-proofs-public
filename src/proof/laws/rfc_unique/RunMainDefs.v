(* The main of harness/rfc_unique.c in pieces: the cut points of its body, the context, the postcondition and the
   precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where T_k
   is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, RunMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_unique.code.
Require Import OpensslPunycode.proof.laws.rfc_unique.RunProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len1 = upto(PTRDIFF_MAX), 1 input1 = any_bytes(len1), 2 len2 =
   upto(PTRDIFF_MAX), 3 input2 = any_bytes(len2), 4 cap = nondet_u32(), 5 out1 = any_uints(cap), 6 out2 =
   any_uints(cap), 7 the NULL test, 8 count1 = cap, 9 count2 = cap, 10 r1 = ossl_punycode_decode(input1, ..),
   11 r2 = ossl_punycode_decode(input2, ..), 12 the test of r1, r2, the counts and the outputs, 13 gp_assert(len1 ==
   len2), 14 literal = last_delimiter(input1, len1), 15 the loop over the octets, 16 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T8 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 8 main_big.
Definition T13 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 13 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* A block of n octets (mblock_uc) or n unsigned ints (mblock_ui) from malloc: NULL, or its token and its
   contents. *)
Definition mblock_uc (n: Z) (v: list val) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) v q.
Definition mblock_ui (n: Z) (v: list val) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuint n) q * data_at Ews (tarray tuint n) v q.

(* What the checks need of two inputs: the conclusion of the model fact RunUniqStmt.unique_stmt (same length; where
   they differ, the position is among the deltas and both octets are the same letter, up to case). *)
Definition same_up_to_case (inp1 inp2: list Z) : Prop :=
  Zlength inp1 = Zlength inp2 /\
  forall j, 0 <= j < Zlength inp1 -> Znth j inp1 <> Znth j inp2 ->
    (last_delim inp1 < j \/ last_delim inp1 = 0) /\
    97 <= Z.lor (Znth j inp1) 32 <= 122 /\ Z.lor (Znth j inp2) 32 = Z.lor (Znth j inp1) 32.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the constants of punycode.c as its specification wants them, mem_mgr). *)
Definition pre0 (gv: globals) (v1 v2: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 7: the two inputs bs1, bs2 (at pi1, pi2), the capacity c and the two arrays out1, out2 of c unsigned ints
   (vs1, vs2) drawn; each block is NULL or from malloc. *)
Definition pre7 (gv: globals) (v1 v2: val) (bs1 bs2: list Z) (pi1 pi2: val) (c: Z) (vs1 vs2: list Z)
    (po1 po2: val) : environ -> mpred :=
  PROP (bytes_ok bs1; bytes_ok bs2; Zlength bs1 <= Int64.max_signed; Zlength bs2 <= Int64.max_signed;
        0 <= c <= Int.max_unsigned; Zlength vs1 = c; Zlength vs2 = c)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr c));
         temp _input2 pi2; temp _len2 (Vlong (Int64.repr (Zlength bs2)));
         temp _input1 pi1; temp _len1 (Vlong (Int64.repr (Zlength bs1)));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (mblock_uc (Zlength bs1) (vb bs1) pi1; mblock_uc (Zlength bs2) (vb bs2) pi2;
       mblock_ui c (vb vs1) po1; mblock_ui c (vb vs2) po2;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 8: past the NULL test: the same, the blocks as arrays (nothing when empty), their tokens dropped. *)
Definition pre8 (gv: globals) (v1 v2: val) (bs1 bs2: list Z) (pi1 pi2: val) (c: Z) (vs1 vs2: list Z)
    (po1 po2: val) : environ -> mpred :=
  PROP (bytes_ok bs1; bytes_ok bs2; Zlength bs1 <= Int64.max_signed; Zlength bs2 <= Int64.max_signed;
        0 <= c <= Int.max_unsigned; Zlength vs1 = c; Zlength vs2 = c)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr c));
         temp _input2 pi2; temp _len2 (Vlong (Int64.repr (Zlength bs2)));
         temp _input1 pi1; temp _len1 (Vlong (Int64.repr (Zlength bs1)));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (arr0 Ews tuchar (Zlength bs1) (vb bs1) pi1; arr0 Ews tuchar (Zlength bs2) (vb bs2) pi2;
       arr0 Ews tuint c (vb vs1) po1; arr0 Ews tuint c (vb vs2) po2;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 13: both decodes succeeded with the same code points, so (model fact) the inputs are the same up to the case
   of letters among the deltas. *)
Definition pre13 (gv: globals) (v1 v2: val) (bs1 bs2: list Z) (pi1 pi2: val) : environ -> mpred :=
  PROP (bytes_ok bs1; bytes_ok bs2; Zlength bs1 <= Int64.max_signed; Zlength bs2 <= Int64.max_signed;
        same_up_to_case bs1 bs2)
  LOCAL (temp _input2 pi2; temp _len2 (Vlong (Int64.repr (Zlength bs2)));
         temp _input1 pi1; temp _len1 (Vlong (Int64.repr (Zlength bs1)));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (arr0 Ews tuchar (Zlength bs1) (vb bs1) pi1; arr0 Ews tuchar (Zlength bs2) (vb bs2) pi2;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece13_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs1 bs2 pi1 pi2,
  semax Delta_main (pre13 gv v1 v2 bs1 bs2 pi1 pi2) (Ssequence T13 ret0) main_post.
Definition piece8_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2,
  semax Delta_main (pre8 gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2) (Ssequence T8 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2,
  semax Delta_main (pre7 gv v1 v2 bs1 bs2 pi1 pi2 c vs1 vs2 po1 po2) (Ssequence T7 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv v1 v2,
  semax Delta_main (pre0 gv v1 v2) (Ssequence T0 ret0) main_post.
