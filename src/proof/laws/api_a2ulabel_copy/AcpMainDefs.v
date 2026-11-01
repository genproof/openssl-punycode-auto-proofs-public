(* The main of harness/api_a2ulabel_copy.c in four pieces: the cut points of its body, the context, the
   postcondition and the precondition at each cut.  A piece is
   `semax Delta_main (pre ...) (Ssequence T ret0) main_post`, where T is the body's top-level sequence from a
   statement on (what VST shows at that point, followed by MORE_COMMANDS = ret0). *)
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

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* T0: the whole body; T6: from `in[len] = 0` on; T9: from the gp_assume loop on; T10: from
   `ossl_shim_zalloc_failed = 0` on (the call of ossl_a2ulabel and the checks). *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.
Definition T9 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 9 main_big.
Definition T10 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 10 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 6: after the NULL tests: in holds len + 1 arbitrary octets bs0, out holds outlen >= 1 arbitrary octets ob,
   saved a copy of them. *)
Definition pre6 (gv: globals) (len: Z) (bs0: list Z) (pin: val) (outlen: Z) (ob: list Z) (pout psaved: val)
    : environ -> mpred :=
  PROP (0 <= len < Int64.max_signed; bytes_ok bs0; Zlength bs0 = (len + 1)%Z; 1 <= outlen <= Int64.max_signed;
        bytes_ok ob; Zlength ob = outlen)
  LOCAL (temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen)); temp _in pin;
         temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at Ews (tarray tuchar (len + 1)) (vb bs0) pin;
       data_at Ews (tarray tuchar outlen) (vb ob) pout;
       data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT).

(* Cut 9: n is the length of the string s of in: in holds s, its NUL, then the rest t of the buffer. *)
Definition pre9 (gv: globals) (len: Z) (s t: list Z) (pin: val) (outlen: Z) (ob: list Z) (pout psaved: val)
    : environ -> mpred :=
  PROP (0 <= len < Int64.max_signed; OpensslPunycode.proof.shim.ShimSpec.str_ok s; bytes_ok t;
        (Zlength s + Zlength t)%Z = len; 1 <= outlen <= Int64.max_signed; bytes_ok ob; Zlength ob = outlen)
  LOCAL (temp _n (Vlong (Int64.repr (Zlength s))); temp _saved psaved; temp _out pout;
         temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
       data_at Ews (tarray tuchar outlen) (vb ob) pout;
       data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT).

(* Cut 10: after the gp_assume loop: in addition, no label of s starts with "xn--" in any case. *)
Definition pre10 (gv: globals) (len: Z) (s t: list Z) (pin: val) (outlen: Z) (ob: list Z) (pout psaved: val)
    : environ -> mpred :=
  PROP (0 <= len < Int64.max_signed; OpensslPunycode.proof.shim.ShimSpec.str_ok s; bytes_ok t;
        (Zlength s + Zlength t)%Z = len; 1 <= outlen <= Int64.max_signed; bytes_ok ob; Zlength ob = outlen;
        acp_noprefix s)
  LOCAL (temp _n (Vlong (Int64.repr (Zlength s))); temp _saved psaved; temp _out pout;
         temp _outlen (Vlong (Int64.repr outlen)); temp _in pin; gvars gv)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at Ews (tarray tuchar (len + 1)) (vb (s ++ [0] ++ t)) pin;
       data_at Ews (tarray tuchar outlen) (vb ob) pout;
       data_at Ews (tarray tuchar outlen) (vb ob) psaved; TT).
