(* The main of harness/api_decode_deterministic.c in pieces: the cut points of its body, the context, the
   postcondition and the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0)
   main_post`, where T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues
   with as a hypothesis, DdetMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_deterministic.code.
Require Import OpensslPunycode.proof.laws.api_decode_deterministic.DdetProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(..), 1 more = upto(..), 2 first = any_bytes(len + more),
   3 second = copy_of(first, len), 4 cap = nondet_u32(), 5 out1 = any_uints(cap), 6 out2 = any_uints(cap),
   7 the NULL test, 8 count1 = cap, 9 count2 = cap, 10 r1 = ossl_punycode_decode(first, ..), 11 r2 =
   ossl_punycode_decode(second, ..), 12 gp_assert(r1 == r2 && count1 == count2), 13 if (r1 == 1)
   gp_assert(uints_eq(..)), 14 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T4 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 4 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T8 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 8 main_big.

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

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) (v1 v2: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 4: first holds the octets bs (len of them, then the others), second a copy of the first len (NULL when first
   is NULL). *)
Definition pre4 (gv: globals) (v1 v2: val) (bs: list Z) (len: Z) (pf ps: val) : environ -> mpred :=
  PROP (bytes_ok bs; 0 <= len <= Zlength bs; Zlength bs <= Int64.max_unsigned; pf = nullval -> ps = nullval)
  LOCAL (temp _second ps; temp _first pf; temp _len (Vlong (Int64.repr len));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (mblock_uc (Zlength bs) (vb bs) pf; mblock_uc len (vb (sublist 0 len bs)) ps;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 7: the capacity c and the two arrays out1, out2 of c unsigned ints (vs1, vs2) drawn. *)
Definition pre7 (gv: globals) (v1 v2: val) (bs: list Z) (len: Z) (pf ps: val) (c: Z) (vs1 vs2: list Z)
    (po1 po2: val) : environ -> mpred :=
  PROP (bytes_ok bs; 0 <= len <= Zlength bs; Zlength bs <= Int64.max_unsigned; pf = nullval -> ps = nullval;
        0 <= c <= Int.max_unsigned; Zlength vs1 = c; Zlength vs2 = c;
        Forall (fun x => 0 <= x <= Int.max_unsigned) vs1; Forall (fun x => 0 <= x <= Int.max_unsigned) vs2)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr c));
         temp _second ps; temp _first pf; temp _len (Vlong (Int64.repr len));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (mblock_uc (Zlength bs) (vb bs) pf; mblock_uc len (vb (sublist 0 len bs)) ps;
       mblock_ui c (vb vs1) po1; mblock_ui c (vb vs2) po2;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 8: past the NULL test: the input inp (the first len octets) at first and at second, the arrays. *)
Definition pre8 (gv: globals) (v1 v2: val) (inp: list Z) (pf ps: val) (c: Z) (vs1 vs2: list Z)
    (po1 po2: val) : environ -> mpred :=
  PROP (bytes_ok inp; Zlength inp <= Int64.max_unsigned;
        0 <= c <= Int.max_unsigned; Zlength vs1 = c; Zlength vs2 = c)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr c));
         temp _second ps; temp _first pf; temp _len (Vlong (Int64.repr (Zlength inp)));
         gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (arr0 Ews tuchar (Zlength inp) (vb inp) pf; arr0 Ews tuchar (Zlength inp) (vb inp) ps;
       arr0 Ews tuint c (vb vs1) po1; arr0 Ews tuint c (vb vs2) po2;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece8_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 inp pf ps c vs1 vs2 po1 po2,
  semax Delta_main (pre8 gv v1 v2 inp pf ps c vs1 vs2 po1 po2) (Ssequence T8 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs len pf ps c vs1 vs2 po1 po2,
  semax Delta_main (pre7 gv v1 v2 bs len pf ps c vs1 vs2 po1 po2) (Ssequence T7 ret0) main_post.
Definition piece4_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs len pf ps,
  semax Delta_main (pre4 gv v1 v2 bs len pf ps) (Ssequence T4 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv v1 v2,
  semax Delta_main (pre0 gv v1 v2) (Ssequence T0 ret0) main_post.
