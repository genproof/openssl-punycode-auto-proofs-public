(* The main of harness/rfc_basic_first.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, RbfMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_basic_first.code.
Require Import OpensslPunycode.proof.laws.rfc_basic_first.RbfProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(PTRDIFF_MAX), 1 input = any_bytes, 2 cap = nondet_u32(),
   3 out = any_uints, 4 the NULL test, 5 literal = last_delimiter, 6 count = cap, 7 r = ossl_punycode_decode,
   8 the loop over the literal octets, 9 the check of the output when r == 1, 10 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T5 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 5 main_big.
Definition T8 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 8 main_big.
Definition T9 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 9 main_big.

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

(* Cut 5: past the NULL test: the input bs, the capacity cap = |init| and the array out holding init. *)
Definition pre5 (gv: globals) (vc: val) (bs: list Z) (pi: val) (init: list Z) (po: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* What the checks need of the decoder's result r, the array a and the count cnt it leaves: r is 0 or 1; a literal
   octet >= 0x80 gives 0; on 1, Model.decode succeeded with out, the count is |out| and the array starts with out. *)
Definition rbf_res (bs: list Z) (cap r: Z) (a: list val) (cnt: Z) : Prop :=
  (r = 0 \/ r = 1) /\ (forall i, 0 <= i < last_delim bs -> 128 <= Znth i bs -> r = 0) /\
  (r = 1 -> exists out tail, decode bs cap = (true, out) /\ cnt = Zlength out /\ a = vb out ++ tail).

(* Cuts 8 and 9: after the decoder (the same state; cut 9 is past the loop over the literal octets). *)
Definition pre8 (gv: globals) (vc: val) (bs: list Z) (pi: val) (cap: Z) (po: val) (r: Z) (a: list val) (cnt: Z)
  : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= cap <= Int.max_unsigned; rbf_res bs cap r a cnt)
  LOCAL (temp _r (Vint (Int.repr r)); temp _literal (Vlong (Int64.repr (last_delim bs))); temp _out po;
         temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint cap a po; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
       data_at Tsh tuint (Vint (Int.repr cnt)) vc; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece9_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi cap po r a cnt,
  semax Delta_main (pre8 gv vc bs pi cap po r a cnt) (Ssequence T9 ret0) main_post.
Definition piece8_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi cap po r a cnt,
  semax Delta_main (pre8 gv vc bs pi cap po r a cnt) (Ssequence T8 ret0) main_post.
Definition piece5_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi init po,
  semax Delta_main (pre5 gv vc bs pi init po) (Ssequence T5 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc,
  semax Delta_main (pre0 gv vc) (Ssequence T0 ret0) main_post.
