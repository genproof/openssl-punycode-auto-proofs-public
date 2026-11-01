(* The main of harness/x_a2ulabel.c in pieces: the cut points of its body, the context, the postcondition and the
   precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where T_k
   is the body's top-level sequence from its k-th statement on (what VST shows at that point, followed by
   MORE_COMMANDS = ret0); it takes the pieces it continues with as hypotheses (no piece Requires another one),
   Main.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* T_k: from the statement `nondet_bytes(in, n)` (6), the loop (10), `ossl_shim_fail_next = ...` (16, after the
   if on mode), the if-chain on the result (20), `if (out != NULL)` (21). *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T5 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 5 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.
Definition T10 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 10 main_big.
Definition T11 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 11 main_big.
Definition T16 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 16 main_big.
Definition T20 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 20 main_big.
Definition T21 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 21 main_big.

(* The then-branch of `if ((mode & 1) == 0)` (statement 15), and the else-branch of `if (t'15)` (in statement 20). *)
Definition S15then : statement :=
  Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in
  match spine_drop 15 main_big with Ssequence (Sifthenelse _ s _) _ => s | s => s end.
Definition S20else : statement :=
  Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in
  match spine_drop 20 main_big with Ssequence (Ssequence _ (Sifthenelse _ _ s)) _ => s | s => s end.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

Definition t_sink := Tstruct _pr_sink noattr.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* The input facts: n octets bs, then the NUL at in[n]; the string s = the first sl octets (none of them 0). *)
Definition in_ok (n: Z) (bs: list Z) : Prop :=
  0 <= n < Int64.max_unsigned /\ bytes_ok bs /\ Zlength bs = n.
Definition sl_ok (n: Z) (bs: list Z) (sl: Z) : Prop :=
  0 <= sl <= n /\ Forall (fun b => b <> 0) (sublist 0 sl bs) /\ Znth sl (bs ++ [0]) = 0.

(* The buffer want: none when out = NULL. *)
Definition want_buf (out want: val) (outlen: Z) (l: list Z) : mpred :=
  if Val.eq out nullval then emp else arr0 Ews tuchar outlen (vb l) want.

(* The token type of a zero-size out buffer (ossl_a2ulabel_spec's tk). *)
Definition tk0 : type := tarray tuchar 0.

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) (v_k: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k; TT).

(* A block of malloc: nothing when it failed. *)
Definition mres (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)%logic.

(* Cut 5: after the three mallocs. *)
Definition pre5 (gv: globals) (v_k: val) (n: Z) (pin psnap pcps: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _cps pcps; temp _snap psnap; temp _in pin; temp _n (Vlong (Int64.repr n)); gvars gv;
         lvar _k t_sink v_k)
  SEP (mem_mgr gv; mres (tarray tuint 512) pcps; mres (tarray tuchar (n + 1)) psnap;
       mres (tarray tuchar (n + 1)) pin; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k; TT).

(* Cut 6: after the three mallocs and their test. *)
Definition pre6 (gv: globals) (v_k: val) (n: Z) (pin psnap pcps: val) : environ -> mpred :=
  PROP (0 <= n < Int64.max_unsigned)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap; temp _cps pcps;
         gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at_ Ews (tarray tuchar (n + 1)) pin; data_at_ Ews (tarray tuchar (n + 1)) psnap;
       data_at_ Ews (tarray tuint 512) pcps; TT).

(* Cut 10: in and snap hold bs ++ [0]; sl = 0. *)
Definition pre10 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (pin psnap pcps: val) : environ -> mpred :=
  PROP (in_ok n bs)
  LOCAL (temp _sl (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps; TT).

(* Cut 11: after the loop, sl = the length of the string. *)
Definition pre11 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val) : environ -> mpred :=
  PROP (in_ok n bs; sl_ok n bs sl)
  LOCAL (temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps; TT).

(* Cut 16: after the if on mode: out is NULL, or out and want are two buffers of outlen octets holding ob (out with
   the token of its malloc(0) block when outlen = 0). *)
Definition pre16 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val)
    (outlen m: Z) (out want: val) (ob: list Z) : environ -> mpred :=
  PROP (in_ok n bs; sl_ok n bs sl; 0 <= outlen <= Int64.max_unsigned; 0 <= m <= Byte.max_unsigned;
        bytes_ok ob; Zlength ob = outlen; is_pointer_or_null out; is_pointer_or_null want)
  LOCAL (temp _want want; temp _out out; temp _mode (Vint (Int.repr m)); temp _outlen (Vlong (Int64.repr outlen));
         temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews out outlen (vb ob) tk0;
       want_buf out want outlen ob; TT).

(* The knob set by the harness from mode. *)
Definition knob (m: Z) : Z := if Z.land m 2 =? 0 then 0 else 1.

(* The outcome of the call ossl_a2ulabel(in, out, outlen) with the knob fn, malloc failing or not (mf). *)
Definition outcome (n: Z) (bs: list Z) (sl: Z) (outlen: Z) (out: val) (ob: list Z) (fn: Z) (mf: bool) :=
  OpensslPunycode.proof.punycode.PunySpec.a2u_outcome out outlen (sublist 0 sl bs) (vb ob) fn 0 mf.

(* Cut 20: after r = ossl_a2ulabel(in, out, outlen). *)
Definition pre20 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val)
    (outlen: Z) (out want: val) (ob: list Z) (fn: Z) (mf: bool) : environ -> mpred :=
  PROP (in_ok n bs; sl_ok n bs sl; 0 <= outlen <= Int64.max_unsigned; fn = 0 \/ fn = 1;
        bytes_ok ob; Zlength ob = outlen; is_pointer_or_null out; is_pointer_or_null want)
  LOCAL (temp _r (Vint (Int.repr (fst (fst (fst (outcome n bs sl outlen out ob fn mf))))));
         temp _want want; temp _out out; temp _outlen (Vlong (Int64.repr outlen));
         temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (OpensslPunycode.proof.shim.ShimSpec.shim_state gv (snd (fst (fst (outcome n bs sl outlen out ob fn mf))))
         (snd (fst (outcome n bs sl outlen out ob fn mf))) 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews out outlen (snd (outcome n bs sl outlen out ob fn mf)) tk0;
       want_buf out want outlen ob; TT).

(* Cut 21: after the check of r: out and want hold the same octets l. *)
Definition pre21 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (pin psnap: val)
    (outlen: Z) (out want: val) (l: list Z) (fn zf: Z) : environ -> mpred :=
  PROP (in_ok n bs; 0 <= outlen <= Int64.max_unsigned; bytes_ok l; Zlength l = outlen;
        is_pointer_or_null out; is_pointer_or_null want)
  LOCAL (temp _want want; temp _out out; temp _outlen (Vlong (Int64.repr outlen));
         temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap; gvars gv; lvar _k t_sink v_k)
  SEP (OpensslPunycode.proof.shim.ShimSpec.shim_state gv fn zf 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       OpensslPunycode.proof.punycode.PunySpec.out_buf Ews out outlen (vb l) tk0;
       want_buf out want outlen l; TT).

(* The then-branch of `if ((mode & 1) == 0)`: its precondition (out = want = NULL so far) and the join of the if. *)
Definition pre15 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val) (outlen m: Z)
    : environ -> mpred :=
  PROP (in_ok n bs; sl_ok n bs sl; 0 <= outlen <= Int64.max_unsigned; 0 <= m <= Byte.max_unsigned)
  LOCAL (temp _want nullval; temp _out nullval; temp _mode (Vint (Int.repr m));
         temp _outlen (Vlong (Int64.repr outlen));
         temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps; TT).

Definition join16 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val) (outlen m: Z)
    : environ -> mpred :=
  EX out: val, EX want: val, EX ob: list Z, pre16 gv v_k n bs sl pin psnap pcps outlen m out want ob.

(* The else-branch of `if (t'15)`: out is a buffer of outlen >= 1 octets, the allocation went through (the knob
   was 0, malloc did not fail), so r and out are the model's. *)
Definition pre20e (gv: globals) (v_k: val) (n: Z) (bs: list Z) (sl: Z) (pin psnap pcps: val)
    (outlen: Z) (out want: val) (ob: list Z) : environ -> mpred :=
  PROP (in_ok n bs; sl_ok n bs sl; 1 <= outlen <= Int64.max_unsigned;
        bytes_ok ob; Zlength ob = outlen; isptr out; is_pointer_or_null want)
  LOCAL (temp _r (Vint (Int.repr (fst (a2ulabel (sublist 0 sl bs) outlen))));
         temp _want want; temp _out out; temp _outlen (Vlong (Int64.repr outlen));
         temp _sl (Vlong (Int64.repr sl)); temp _n (Vlong (Int64.repr n)); temp _in pin; temp _snap psnap;
         temp _cps pcps; gvars gv; lvar _k t_sink v_k)
  SEP (OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       data_at_ Tsh t_sink v_k;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) pin;
       data_at Ews (tarray tuchar (n + 1)) (vb (bs ++ [0])) psnap;
       data_at_ Ews (tarray tuint 512) pcps;
       data_at Ews (tarray tuchar outlen)
         (vb (snd (a2ulabel (sublist 0 sl bs) outlen)) ++
          sublist (Zlength (snd (a2ulabel (sublist 0 sl bs) outlen))) outlen (vb ob)) out;
       data_at Ews (tarray tuchar outlen) (vb ob) want; TT).

Definition join21 (gv: globals) (v_k: val) (n: Z) (bs: list Z) (pin psnap: val) (outlen: Z) (out want: val)
    : environ -> mpred :=
  EX l: list Z, EX fn: Z, EX zf: Z, pre21 gv v_k n bs pin psnap outlen out want l fn zf.
