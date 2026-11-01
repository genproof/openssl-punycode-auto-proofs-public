(* The main of harness/api_decode_capacity.c in pieces: the cut points of its body, the context, the postcondition
   and the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`,
   where T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, DcapMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(..), 1 input = any_bytes(len), 2 cap = nondet_u32(),
   3 out = any_uints(cap), 4 saved = malloc(cap * 4), 5 the NULL test, 6 the copy loop into saved, 7 count = cap,
   8 the first ossl_punycode_decode and its test, 9 the check of the elements from count on, 10 exact =
   any_uints(count), 11 exact_count = count, 12 the NULL test of exact, 13 the decode into exact and its check,
   14 the check of exact_count and the elements, 15 the decode into count - 1 elements (count > 0), 16 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T5 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 5 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T10 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 10 main_big.
Definition T15 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 15 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* A block from malloc: NULL, or its token and its contents: n octets (mblock_uc), n unsigned ints (mblock_ui),
   n uninitialised unsigned ints (mblock_un). *)
Definition mblock_uc (n: Z) (v: list val) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) v q.
Definition mblock_ui (n: Z) (v: list val) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuint n) q * data_at Ews (tarray tuint n) v q.
Definition mblock_un (n: Z) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray tuint n) q * data_at_ Ews (tarray tuint n) q.

(* The locals of main: count, exact_count, fewer_count. *)
Definition lvars3 (vc ve vf: val) : list localdef :=
  [lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf].

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) (vc ve vf: val) : environ -> mpred :=
  PROPx []
  (LOCALx (gvars gv :: lvars3 vc ve vf)
  (SEPx [data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* Cut 5: the input bs at input, the capacity c, the array out of c unsigned ints init, the block saved. *)
Definition pre5 (gv: globals) (vc ve vf: val) (bs: list Z) (pi: val) (c: Z) (init: list Z) (po ps: val)
    : environ -> mpred :=
  PROPx [bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned; Zlength init = c;
         Forall (fun x => 0 <= x <= Int.max_unsigned) init]
  (LOCALx (temp _saved ps :: temp _out po :: temp _cap (Vint (Int.repr c)) :: temp _input pi ::
           temp _len (Vlong (Int64.repr (Zlength bs))) :: gvars gv :: lvars3 vc ve vf)
  (SEPx [mblock_uc (Zlength bs) (vb bs) pi; mblock_ui c (vb init) po; mblock_un c ps;
         data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* Cut 6: past the NULL test: the blocks as arrays (nothing when empty), saved uninitialised; out and saved are
   pointers (the check computes out + count and saved + count even when cap = 0). *)
Definition pre6 (gv: globals) (vc ve vf: val) (bs: list Z) (pi: val) (c: Z) (init: list Z) (po ps: val)
    : environ -> mpred :=
  PROPx [bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned; Zlength init = c;
         Forall (fun x => 0 <= x <= Int.max_unsigned) init;
         isptr po; isptr ps]
  (LOCALx (temp _saved ps :: temp _out po :: temp _cap (Vint (Int.repr c)) :: temp _input pi ::
           temp _len (Vlong (Int64.repr (Zlength bs))) :: gvars gv :: lvars3 vc ve vf)
  (SEPx [arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint c (vb init) po;
         arr0 Ews tuint c (Zrepeat Vundef c) ps;
         data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* Cut 7: past the copy loop: saved holds the initial values of out. *)
Definition pre7 (gv: globals) (vc ve vf: val) (bs: list Z) (pi: val) (c: Z) (init: list Z) (po ps: val)
    : environ -> mpred :=
  PROPx [bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned; Zlength init = c;
         Forall (fun x => 0 <= x <= Int.max_unsigned) init;
         isptr po; isptr ps]
  (LOCALx (temp _saved ps :: temp _out po :: temp _cap (Vint (Int.repr c)) :: temp _input pi ::
           temp _len (Vlong (Int64.repr (Zlength bs))) :: gvars gv :: lvars3 vc ve vf)
  (SEPx [arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint c (vb init) po;
         arr0 Ews tuint c (vb init) ps;
         data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* The model facts past the first decode, which returned 1 with the code points out: the same decode into exactly
   Zlength out elements, a failure into one fewer. *)
Definition dcap_facts (bs out: list Z) : Prop :=
  Zlength bs < Int.max_unsigned /\ Zlength out <= Int.max_unsigned /\
  Forall (fun x => 0 <= x <= Int.max_unsigned) out /\
  decode bs (Zlength out) = (true, out) /\
  (out <> [] -> fst (decode bs (Zlength out - 1)) = false).

(* Cut 10: past the first check: count holds Zlength out, the first Zlength out elements of out are out. *)
Definition pre10 (gv: globals) (vc ve vf: val) (bs: list Z) (pi: val) (out: list Z) (po: val)
    : environ -> mpred :=
  PROPx [bytes_ok bs; dcap_facts bs out]
  (LOCALx (temp _out po :: temp _input pi :: temp _len (Vlong (Int64.repr (Zlength bs))) ::
           gvars gv :: lvars3 vc ve vf)
  (SEPx [arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint (Zlength out) (vb out) po;
         data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* Cut 15: past the checks of the decode into exactly Zlength out elements (exact_count is kept as a block for
   main's stack frame). *)
Definition pre15 (gv: globals) (vc ve vf: val) (bs: list Z) (pi: val) (out: list Z)
    : environ -> mpred :=
  PROPx [bytes_ok bs; dcap_facts bs out]
  (LOCALx (temp _input pi :: temp _len (Vlong (Int64.repr (Zlength bs))) :: gvars gv :: lvars3 vc ve vf)
  (SEPx [arr0 Ews tuchar (Zlength bs) (vb bs) pi;
         data_at Tsh tuint (Vint (Int.repr (Zlength out))) vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
         OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT])).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece15_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf bs pi out,
  semax Delta_main (pre15 gv vc ve vf bs pi out) (Ssequence T15 ret0) main_post.
Definition piece10_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf bs pi out po,
  semax Delta_main (pre10 gv vc ve vf bs pi out po) (Ssequence T10 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf bs pi c init po ps,
  semax Delta_main (pre7 gv vc ve vf bs pi c init po ps) (Ssequence T7 ret0) main_post.
Definition piece6_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf bs pi c init po ps,
  semax Delta_main (pre6 gv vc ve vf bs pi c init po ps) (Ssequence T6 ret0) main_post.
Definition piece5_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf bs pi c init po ps,
  semax Delta_main (pre5 gv vc ve vf bs pi c init po ps) (Ssequence T5 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc ve vf,
  semax Delta_main (pre0 gv vc ve vf) (Ssequence T0 ret0) main_post.
