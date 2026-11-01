(* The main of harness/rj_decode_any.c in pieces: the cut points of its body, the context, the postcondition and the
   precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where T_k
   is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, JdaMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rj_decode_any.code.
Require Import OpensslPunycode.proof.laws.rj_decode_any.JdaProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(PTRDIFF_MAX), 1 input = any_bytes, 2 saved = copy_of,
   3 cap = nondet_u32(), 4 out = any_uints, 5 the NULL test, 6 count = cap, 7 r = ossl_punycode_decode,
   8 gp_assert(r == 1 || r == 0), 9 gp_assert(r == 1 ? count <= cap : count == cap),
   10 gp_assert(bytes_eq(input, saved, len)), 11 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the constants of punycode.c as its specification wants them, mem_mgr). *)
Definition pre0 (gv: globals) (vc: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count tuint vc)
  SEP (data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 6: past the NULL test: the input bs and its copy (two blocks of |bs| octets, none when bs = []), the
   capacity cap = |init| and the array out holding init. *)
Definition pre6 (gv: globals) (vc: val) (bs: list Z) (pi ps: val) (init: list Z) (po: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _saved ps; temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece6_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi ps init po,
  semax Delta_main (pre6 gv vc bs pi ps init po) (Ssequence T6 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc,
  semax Delta_main (pre0 gv vc) (Ssequence T0 ret0) main_post.
