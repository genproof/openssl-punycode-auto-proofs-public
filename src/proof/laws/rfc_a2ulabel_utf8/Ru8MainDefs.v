(* The main of harness/rfc_a2ulabel_utf8.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on (what VST shows at that point, followed by
   MORE_COMMANDS = ret0); it takes the piece it continues with as a hypothesis (no piece Requires another one),
   Ru8Main.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto, 1 label = any_bytes, 2 cps = malloc, 3 outlen = upto,
   4 out = any_bytes, 5 saved = copy_of, 6 want = malloc, 7 the NULL test, 8-12 the octets "xn--" and the NUL of
   label, 13 the gp_assume loop, 14 count = 512, 15 valid = decode(..) == 1, 16 size = 0, 17 the utf8 loop,
   18 want[size] = 0, 19 size++, 20 ossl_shim_zalloc_failed = 0, 21 r = ossl_a2ulabel, 22 the checks,
   23 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T13 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 13 main_big.
Definition T14 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 14 main_big.
Definition T17 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 17 main_big.
Definition T20 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 20 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* A block of type t from malloc that may be NULL: its token and its contents, each emp when it is NULL. *)
Definition btok (t: type) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews t q.
Definition bdat (t: type) (v: reptype t) (q: val) : mpred :=
  if eq_dec q nullval then emp else data_at Ews t v q.

(* What ossl_punycode_decode(label + 4, len, cps, &count) returns, leaves in cps and in count (cps uninitialized,
   count = 512). *)
Definition dres (s: list Z) : Z * list val * Z :=
  OpensslPunycode.proof.punycode.PunySpec.decode_result s 512 (Zrepeat Vundef 512).

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr, the local count). *)
Definition pre0 (gv: globals) (vc: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count tuint vc)
  SEP (data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 7: the draws done: label of len + 5 octets lbs, cps of 512 unsigned ints, out of outlen octets ob, saved a
   copy of them, want of 2049 octets; each block NULL when its malloc failed (saved also when out is NULL). *)
Definition pre7 (gv: globals) (vc: val) (len: Z) (lbs: list Z) (pl pc: val) (outlen: Z) (ob: list Z)
    (pout psaved pw: val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength lbs = (len + 5)%Z; bytes_ok lbs;
        0 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout = nullval -> psaved = nullval)
  LOCAL (temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (btok (tarray tuchar (len + 5)) pl; bdat (tarray tuchar (len + 5)) (vb lbs) pl;
       btok (tarray tuint 512) pc; bdat (tarray tuint 512) (Zrepeat Vundef 512) pc;
       btok (tarray tuchar outlen) pout; bdat (tarray tuchar outlen) (vb ob) pout;
       btok (tarray tuchar outlen) psaved; bdat (tarray tuchar outlen) (vb ob) psaved;
       btok (tarray tuchar 2049) pw; bdat (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 13: past the NULL test (outlen >= 1, every block there) and the octets "xn--" and the NUL of label: label
   holds xn ++ s ++ [0] with s any len octets. *)
Definition pre13 (gv: globals) (vc: val) (len: Z) (s: list Z) (pl pc: val) (outlen: Z) (ob: list Z)
    (pout psaved pw: val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength s = len; bytes_ok s;
        1 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout <> nullval)
  LOCAL (temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) (Zrepeat Vundef 512) pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 14: past the gp_assume loop: no octet of s is '.' or NUL. *)
Definition pre14 (gv: globals) (vc: val) (len: Z) (s: list Z) (pl pc: val) (outlen: Z) (ob: list Z)
    (pout psaved pw: val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength s = len; bytes_ok s;
        Forall (fun c => c <> 46 /\ c <> 0) s;
        1 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout <> nullval)
  LOCAL (temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) (Zrepeat Vundef 512) pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 17: past count = 512, valid = ossl_punycode_decode(label + 4, len, cps, &count) == 1 and size = 0: cps and
   count as decode_result says. *)
Definition pre17 (gv: globals) (vc: val) (len: Z) (s: list Z) (pl pc: val) (outlen: Z) (ob: list Z)
    (pout psaved pw: val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength s = len; bytes_ok s;
        Forall (fun c => c <> 46 /\ c <> 0) s;
        1 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout <> nullval)
  LOCAL (temp _size (Vlong (Int64.repr 0)); temp _valid (Vint (Int.repr (if fst (fst (dres s)) =? 1 then 1 else 0)));
         temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) (snd (fst (dres s))) pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at Tsh tuint (Vint (Int.repr (snd (dres s)))) vc; mem_mgr gv;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* Cut 20: past the utf8 loop, want[size] = 0 and size++: valid says whether the decoding exists (ru8_want); if it
   does, want starts with its octets w and the NUL, and size is |w| + 1. *)
Definition pre20 (gv: globals) (vc: val) (len: Z) (s: list Z) (pl: val) (outlen: Z) (ob: list Z)
    (pout psaved pw: val) (sz: Z) (wv: list val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength s = len; bytes_ok s;
        Forall (fun c => c <> 46 /\ c <> 0) s;
        1 <= outlen <= Int64.max_signed; Zlength ob = outlen; bytes_ok ob; pout <> nullval;
        Zlength wv = 2049;
        match ru8_want s with
        | Some w => sz = (Zlength w + 1)%Z /\ Zlength w <= 2048 /\ sublist 0 sz wv = vb (w ++ [0])
        | None => True
        end)
  LOCAL (temp _size (Vlong (Int64.repr sz));
         temp _valid (Vint (Int.repr (match ru8_want s with Some _ => 1 | None => 0 end)));
         temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _label pl; gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuchar 2049) wv pw;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at_ Tsh tuint vc; mem_mgr gv;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece20_stmt : Prop := forall (Espec: OracleKind) gv vc len s pl outlen ob pout psaved pw sz wv,
  semax Delta_main (pre20 gv vc len s pl outlen ob pout psaved pw sz wv) (Ssequence T20 ret0) main_post.
Definition piece17_stmt : Prop := forall (Espec: OracleKind) gv vc len s pl pc outlen ob pout psaved pw,
  semax Delta_main (pre17 gv vc len s pl pc outlen ob pout psaved pw) (Ssequence T17 ret0) main_post.
Definition piece14_stmt : Prop := forall (Espec: OracleKind) gv vc len s pl pc outlen ob pout psaved pw,
  semax Delta_main (pre14 gv vc len s pl pc outlen ob pout psaved pw) (Ssequence T14 ret0) main_post.
Definition piece13_stmt : Prop := forall (Espec: OracleKind) gv vc len s pl pc outlen ob pout psaved pw,
  semax Delta_main (pre13 gv vc len s pl pc outlen ob pout psaved pw) (Ssequence T13 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv vc len lbs pl pc outlen ob pout psaved pw,
  semax Delta_main (pre7 gv vc len lbs pl pc outlen ob pout psaved pw) (Ssequence T7 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc,
  semax Delta_main (pre0 gv vc) (Ssequence T0 ret0) main_post.
