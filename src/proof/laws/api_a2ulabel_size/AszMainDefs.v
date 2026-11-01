(* The main of harness/api_a2ulabel_size.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, AszMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(PTRDIFF_MAX - 1), 1 in = any_bytes(len + 1),
   2 biglen = nondet_size(), 3 big = any_bytes(biglen), 4 outlen = nondet_size(), 5 out = any_bytes(outlen),
   6 the NULL test, 7 in[len] = 0, 8 ossl_shim_zalloc_failed = 0, 9 r1 = ossl_a2ulabel(in, big, biglen),
   10 r = ossl_a2ulabel(in, out, outlen), 11 the test of the failure flag and of r1, 12 size = 0, 13 the loop
   to the first NUL of big, 14 size++, 15 the checks, then return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T9 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 9 main_big.
Definition T12 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 12 main_big.
Definition T15 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 15 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The token type of a zero-size out buffer (ossl_a2ulabel_spec's tk). *)
Definition tk0 : type := tarray tuchar 0.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 9 (the first call): in holds the len octets bs then a NUL; big holds the biglen octets bb, out the outlen
   octets ob (outlen > 0), both as ossl_a2ulabel's out buffers (big with the token of its block when biglen = 0). *)
Definition pre9 (gv: globals) (len: Z) (bs: list Z) (pin: val) (biglen: Z) (pbig: val) (bb: list Z)
    (outlen: Z) (pout: val) (ob: list Z) : environ -> mpred :=
  PROP (0 <= len < Int64.max_signed; bytes_ok bs; Zlength bs = len;
        0 <= biglen <= Int64.max_unsigned; bytes_ok bb; Zlength bb = biglen;
        0 < outlen <= Int64.max_unsigned; bytes_ok ob; Zlength ob = outlen; pbig <> nullval; pout <> nullval)
  LOCAL (temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig;
         temp _biglen (Vlong (Int64.repr biglen)); temp _in pin; temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pbig biglen (vb bb) tk0;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews pout outlen (vb ob) tk0; TT).

(* Cut 12 (past the test of r1 and the failure flag): the first call gave 1 and wrote w' ++ [0] to big (w' without
   NUL, then the rest tb of big); the second gave r and left ov in out: r = 1 with the same octets first when they
   fit in outlen, else r = 0. *)
Definition pre12 (gv: globals) (biglen: Z) (pbig: val) (w': list Z) (tb: list val) (outlen: Z) (pout: val)
    (ov: list val) (r: Z) : environ -> mpred :=
  PROP (Zlength w' + 1 <= biglen <= Int64.max_unsigned; Forall (fun b => 1 <= b <= 255) w';
        0 < outlen <= Int64.max_unsigned;
        Zlength w' + 1 <= outlen -> r = 1 /\ sublist 0 (Zlength w' + 1) ov = vb (w' ++ [0]);
        outlen < Zlength w' + 1 -> r = 0)
  LOCAL (temp _r (Vint (Int.repr r)); temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig;
         temp _biglen (Vlong (Int64.repr biglen)); gvars gv)
  SEP (data_at Ews (tarray tuchar biglen) (vb (w' ++ [0]) ++ tb) pbig; data_at Ews (tarray tuchar outlen) ov pout;
       TT).

(* Cut 15 (past the loop and size++): size is the number of octets of big up to and with its first NUL. *)
Definition pre15 (gv: globals) (biglen: Z) (pbig: val) (w': list Z) (tb: list val) (outlen: Z) (pout: val)
    (ov: list val) (r: Z) : environ -> mpred :=
  PROP (Zlength w' + 1 <= biglen <= Int64.max_unsigned; Forall (fun b => 1 <= b <= 255) w';
        0 < outlen <= Int64.max_unsigned;
        Zlength w' + 1 <= outlen -> r = 1 /\ sublist 0 (Zlength w' + 1) ov = vb (w' ++ [0]);
        outlen < Zlength w' + 1 -> r = 0)
  LOCAL (temp _size (Vlong (Int64.repr (Zlength w' + 1))); temp _r (Vint (Int.repr r)); temp _out pout;
         temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig; temp _biglen (Vlong (Int64.repr biglen));
         gvars gv)
  SEP (data_at Ews (tarray tuchar biglen) (vb (w' ++ [0]) ++ tb) pbig; data_at Ews (tarray tuchar outlen) ov pout;
       TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece15_stmt : Prop := forall (Espec: OracleKind) gv biglen pbig w' tb outlen pout ov r,
  semax Delta_main (pre15 gv biglen pbig w' tb outlen pout ov r) (Ssequence T15 ret0) main_post.
Definition piece12_stmt : Prop := forall (Espec: OracleKind) gv biglen pbig w' tb outlen pout ov r,
  semax Delta_main (pre12 gv biglen pbig w' tb outlen pout ov r) (Ssequence T12 ret0) main_post.
Definition piece9_stmt : Prop := forall (Espec: OracleKind) gv len bs pin biglen pbig bb outlen pout ob,
  semax Delta_main (pre9 gv len bs pin biglen pbig bb outlen pout ob) (Ssequence T9 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv,
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
