(* The main of harness/api_a2ulabel_nul.c in two pieces: the cut point of its body (the call of ossl_a2ulabel), the
   context, the postcondition and the precondition at the cut.  A piece is
   `semax Delta_main (pre ...) (Ssequence T ret0) main_post`, where T is the body's top-level sequence from a
   statement on (what VST shows at that point, followed by MORE_COMMANDS = ret0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_nul.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_nul.AnuProg.

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* T0: the whole body; T7: from `r = ossl_a2ulabel(in, out, outlen)` on. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The token type of a zero-size out buffer (ossl_a2ulabel_spec's tk). *)
Definition tk0 : type := tarray tuchar 0.

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 7: in holds the len octets bs then a NUL; out is a buffer of outlen octets ob (with the token of its
   malloc(0) block when outlen = 0) and saved a copy of them. *)
Definition pre7 (gv: globals) (len: Z) (bs: list Z) (pin: val) (outlen: Z) (out psaved: val) (ob: list Z)
    : environ -> mpred :=
  PROP (0 <= len < Int64.max_signed; bytes_ok bs; Zlength bs = len; 0 <= outlen <= Int64.max_unsigned;
        bytes_ok ob; Zlength ob = outlen; out <> nullval; psaved <> nullval)
  LOCAL (temp _saved psaved; temp _out out; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin;
         temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at Ews (tarray tuchar (len + 1)) (vb (bs ++ [0])) pin;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews out outlen (vb ob) tk0;
       data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT).
