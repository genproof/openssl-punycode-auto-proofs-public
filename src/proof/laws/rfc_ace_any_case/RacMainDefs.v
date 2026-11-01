(* The main of harness/rfc_ace_any_case.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, RacMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_ace_any_case.code.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacProg.
Require Import OpensslPunycode.proof.laws.rfc_ace_any_case.RacModel.
Local Open Scope logic.
Local Open Scope Z_scope.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module SS := OpensslPunycode.proof.shim.ShimSpec.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(PTRDIFF_MAX - 5), 1 any_case = any_bytes(len + 5),
   2 outlen = nondet_size(), 3 out1 = any_bytes(outlen), 4 out2 = copy_of(out1, outlen), 5 the NULL test,
   6 any_case[0] = 'X' or 'x', 7 any_case[1] = 'N' or 'n', 8 any_case[2] = '-', 9 any_case[3] = '-',
   10 any_case[len + 4] = 0, 11 lower = copy_of(any_case, len + 5), 12 its NULL test, 13 lower[0] = 'x',
   14 lower[1] = 'n', 15 ossl_shim_zalloc_failed = 0, 16 r1 = ossl_a2ulabel(any_case, out1, outlen),
   17 failed1 = ossl_shim_zalloc_failed, 18 ossl_shim_zalloc_failed = 0, 19 r2 = ossl_a2ulabel(lower, out2, outlen),
   20 the test of failed1, 21 the check and return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.
Definition T15 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 15 main_big.
Definition T19 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 19 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------- *)
(* The strings and the outcomes of the two calls                            *)
(* ---------------------------------------------------------------------- *)

(* The string ossl_a2ulabel reads from an array holding the prefix [a; b; '-'; '-'], the octets t, then a NUL: the
   prefix and the octets of t before its first NUL. *)
Definition rstr (a b: Z) (t: list Z) : list Z := [a; b; 45; 45] ++ sublist 0 (nul_len (t ++ [0])) (t ++ [0]).

(* The outcome of ossl_a2ulabel(string, out, outlen) with the knob 0, the failure flag 0 and the buffer holding ob,
   malloc failing or not (mf): (result, knob', flag', buffer'). *)
Definition outc (out: val) (outlen: Z) (s: list Z) (ob: list Z) (mf: bool) : Z * Z * Z * list val :=
  PS.a2u_outcome out outlen s (vb ob) 0 0 mf.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv)
  SEP (PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 6: past the NULL test: any_case holds len + 5 arbitrary octets bs, out1 and out2 hold the same outlen
   arbitrary octets ob; each block with its malloc token (as any_bytes and copy_of give it). *)
Definition pre6 (gv: globals) (len: Z) (bs: list Z) (outlen: Z) (ob: list Z) (pa po1 po2: val) : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength bs = (len + 5)%Z; bytes_ok bs;
        0 <= outlen <= Int64.max_unsigned; Zlength ob = outlen; bytes_ok ob;
        pa <> nullval; po1 <> nullval; po2 <> nullval)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _outlen (Vlong (Int64.repr outlen)); temp _any_case pa;
         temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (@malloc_token HelperSpec.CS Ews (tarray tuchar (len + 5)) pa;
       data_at Ews (tarray tuchar (len + 5)) (vb bs) pa;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po1; data_at Ews (tarray tuchar outlen) (vb ob) po1;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po2; data_at Ews (tarray tuchar outlen) (vb ob) po2;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 15: past the writes: any_case holds [a; b; '-'; '-'] ++ t ++ [0] (a = 'X' or 'x', b = 'N' or 'n'), lower holds
   "xn--" ++ t ++ [0]. *)
Definition pre15 (gv: globals) (len a b: Z) (t: list Z) (outlen: Z) (ob: list Z) (pa pl po1 po2: val)
  : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength t = len; bytes_ok t; a = 88 \/ a = 120; b = 78 \/ b = 110;
        0 <= outlen <= Int64.max_unsigned; Zlength ob = outlen; bytes_ok ob;
        pa <> nullval; pl <> nullval; po1 <> nullval; po2 <> nullval)
  LOCAL (temp _lower pl; temp _out2 po2; temp _out1 po1; temp _outlen (Vlong (Int64.repr outlen));
         temp _any_case pa; temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (@malloc_token HelperSpec.CS Ews (tarray tuchar (len + 5)) pa;
       data_at Ews (tarray tuchar (len + 5)) (vb ([a; b; 45; 45] ++ t ++ [0])) pa;
       @malloc_token HelperSpec.CS Ews (tarray tuchar (len + 5)) pl;
       data_at Ews (tarray tuchar (len + 5)) (vb ([120; 110; 45; 45] ++ t ++ [0])) pl;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po1; data_at Ews (tarray tuchar outlen) (vb ob) po1;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po2; data_at Ews (tarray tuchar outlen) (vb ob) po2;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 19: past the first call (malloc failed in it or not: mf1), failed1 and the reset of the failure flag: r1,
   failed1 and out1 are those of its outcome. *)
Definition pre19 (gv: globals) (len a b: Z) (t: list Z) (outlen: Z) (ob: list Z) (pa pl po1 po2: val) (mf1: bool)
  : environ -> mpred :=
  PROP (0 <= len <= Int64.max_signed - 5; Zlength t = len; bytes_ok t; a = 88 \/ a = 120; b = 78 \/ b = 110;
        0 <= outlen <= Int64.max_unsigned; Zlength ob = outlen; bytes_ok ob;
        pa <> nullval; pl <> nullval; po1 <> nullval; po2 <> nullval)
  LOCAL (temp _failed1 (Vint (Int.repr (snd (fst (outc po1 outlen (rstr a b t) ob mf1)))));
         temp _r1 (Vint (Int.repr (fst (fst (fst (outc po1 outlen (rstr a b t) ob mf1))))));
         temp _lower pl; temp _out2 po2; temp _out1 po1; temp _outlen (Vlong (Int64.repr outlen));
         temp _any_case pa; temp _len (Vlong (Int64.repr len)); gvars gv)
  SEP (@malloc_token HelperSpec.CS Ews (tarray tuchar (len + 5)) pa;
       data_at Ews (tarray tuchar (len + 5)) (vb ([a; b; 45; 45] ++ t ++ [0])) pa;
       @malloc_token HelperSpec.CS Ews (tarray tuchar (len + 5)) pl;
       data_at Ews (tarray tuchar (len + 5)) (vb ([120; 110; 45; 45] ++ t ++ [0])) pl;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po1;
       data_at Ews (tarray tuchar outlen) (snd (outc po1 outlen (rstr a b t) ob mf1)) po1;
       @malloc_token HelperSpec.CS Ews (tarray tuchar outlen) po2; data_at Ews (tarray tuchar outlen) (vb ob) po2;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece19_stmt : Prop := forall (Espec: OracleKind) gv len a b t outlen ob pa pl po1 po2 mf1,
  semax Delta_main (pre19 gv len a b t outlen ob pa pl po1 po2 mf1) (Ssequence T19 ret0) main_post.
Definition piece15_stmt : Prop := forall (Espec: OracleKind) gv len a b t outlen ob pa pl po1 po2,
  semax Delta_main (pre15 gv len a b t outlen ob pa pl po1 po2) (Ssequence T15 ret0) main_post.
Definition piece6_stmt : Prop := forall (Espec: OracleKind) gv len bs outlen ob pa po1 po2,
  semax Delta_main (pre6 gv len bs outlen ob pa po1 po2) (Ssequence T6 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv,
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
