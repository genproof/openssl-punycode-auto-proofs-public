(* The main of harness/rt_roundtrip.c in pieces: the cut points of its body, the context, the postcondition and the
   precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where T_k
   is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, TrtMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 m = upto(PTRDIFF_MAX / 4), 1 room = upto(PTRDIFF_MAX),
   2 cps = any_uints(m), 3 out = any_uints(m), 4 encoding = malloc(room), 5 the NULL tests, the call of encode and
   the test of len, 6 largest = 0, 7 the loop computing largest, 8 count = m, 9 r = ossl_punycode_decode,
   10 the first check, 11 the second check, 12 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T5 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 5 main_big.
Definition T6 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 6 main_big.
Definition T8 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 8 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* A block from malloc that may be NULL: its token and its contents (as arr0), each emp when it is NULL.  Kept
   folded in the main: VST's automation is slow on the conditionals of the unfolded form. *)
Definition jtok {cs: compspecs} (t: type) (n: Z) (q: val) : mpred :=
  if eq_dec q nullval then emp else malloc_token Ews (tarray t n) q.
Definition jarr {cs: compspecs} (t: type) (n: Z) (v: list (reptype t)) (q: val) : mpred :=
  if eq_dec q nullval then emp else arr0 Ews t n v q.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the constants of punycode.c as its specification wants them, mem_mgr). *)
Definition pre0 (gv: globals) (vl vc: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _len tulong vl; lvar _count tuint vc)
  SEP (data_at_ Tsh tulong vl; data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

(* Cut 5: the three blocks drawn, each NULL or not: the code points cps (m = |cps| of them), the array out holding
   outs, the room octets of the encoding (uninitialised). *)
Definition pre5 (gv: globals) (vl vc: val) (cps outs: list Z) (room: Z) (pc po pe: val) : environ -> mpred :=
  PROP (Zlength outs = Zlength cps; 4 * Zlength cps <= Int64.max_unsigned; 0 <= room <= Int64.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) cps; Forall (fun x => 0 <= x <= Int.max_unsigned) outs)
  LOCAL (temp _encoding pe; temp _out po; temp _cps pc; temp _room (Vlong (Int64.repr room));
         temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _len tulong vl; lvar _count tuint vc)
  SEP (@jtok HelperSpec.CS tuint (Zlength cps) pc; @jarr HelperSpec.CS tuint (Zlength cps) (vb cps) pc;
       @jtok HelperSpec.CS tuint (Zlength cps) po; @jarr HelperSpec.CS tuint (Zlength cps) (vb outs) po;
       jtok tuchar room pe; jarr tuchar room (Zrepeat Vundef room) pe;
       data_at_ Tsh tulong vl; data_at_ Tsh tuint vc; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

(* Cut 6: past the test: encode succeeded with the encoding e, of fewer than 2^32 - 1 octets, at the start of the
   block pe (its other octets are dropped), len = |e|. *)
Definition pre6 (gv: globals) (vl vc: val) (cps outs e: list Z) (pc po pe: val) : environ -> mpred :=
  PROP (Zlength outs = Zlength cps; 4 * Zlength cps <= Int64.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) cps; Forall (fun x => 0 <= x <= Int.max_unsigned) outs;
        encode cps = Some e; Zlength e < Int.max_unsigned)
  LOCAL (temp _encoding pe; temp _out po; temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
         gvars gv; lvar _len tulong vl; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength cps) (vb cps) pc; arr0 Ews tuint (Zlength cps) (vb outs) po;
       arr0 Ews tuchar (Zlength e) (vb e) pe;
       data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) vl; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 8: past the loop: largest holds the largest code point (0 for none). *)
Definition pre8 (gv: globals) (vl vc: val) (cps outs e: list Z) (pc po pe: val) : environ -> mpred :=
  PROP (Zlength outs = Zlength cps; 4 * Zlength cps <= Int64.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) cps; Forall (fun x => 0 <= x <= Int.max_unsigned) outs;
        encode cps = Some e; Zlength e < Int.max_unsigned)
  LOCAL (temp _largest (Vlong (Int64.repr (largest cps)));
         temp _encoding pe; temp _out po; temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
         gvars gv; lvar _len tulong vl; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength cps) (vb cps) pc; arr0 Ews tuint (Zlength cps) (vb outs) po;
       arr0 Ews tuchar (Zlength e) (vb e) pe;
       data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) vl; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece8_stmt : Prop := forall (Espec: OracleKind) gv vl vc cps outs e pc po pe,
  semax Delta_main (pre8 gv vl vc cps outs e pc po pe) (Ssequence T8 ret0) main_post.
Definition piece6_stmt : Prop := forall (Espec: OracleKind) gv vl vc cps outs e pc po pe,
  semax Delta_main (pre6 gv vl vc cps outs e pc po pe) (Ssequence T6 ret0) main_post.
Definition piece5_stmt : Prop := forall (Espec: OracleKind) gv vl vc cps outs room pc po pe,
  semax Delta_main (pre5 gv vl vc cps outs room pc po pe) (Ssequence T5 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vl vc,
  semax Delta_main (pre0 gv vl vc) (Ssequence T0 ret0) main_post.
