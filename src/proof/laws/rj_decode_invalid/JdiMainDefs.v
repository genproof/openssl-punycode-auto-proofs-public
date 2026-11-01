(* The main of harness/rj_decode_invalid.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, JdiMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rj_decode_invalid.code.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiProg.
Require Import OpensslPunycode.proof.laws.rj_decode_invalid.JdiModel.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = upto(PTRDIFF_MAX), 1 input = any_bytes, 2 cap = nondet_u32(),
   3 out = any_uints, 4 the NULL test, 5 literal = last_delimiter, 6 deltas, 7 invalid = 0, 8 the loop over the
   octets, 9 count = cap, 10 r = ossl_punycode_decode, 11 the check, 12 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T5 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 5 main_big.
Definition T8 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 8 main_big.
Definition T9 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 9 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* What the loop has found in the octets so far: invalid is 0, or 1 with a flagged octet. *)
Definition flag_ok (bs: list Z) (v: Z) : Prop :=
  v = 0 \/ (v = 1 /\ exists q, 0 <= q < Zlength bs /\ jdi_bad bs q).

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
  PROP (bytes_ok bs; Zlength bs <= Int64.max_signed; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 8: before the loop: literal = last_delim bs, deltas = jdi_start bs, invalid = 0. *)
Definition pre8 (gv: globals) (vc: val) (bs: list Z) (pi: val) (init: list Z) (po: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_signed; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _invalid (Vint (Int.repr 0)); temp _deltas (Vlong (Int64.repr (jdi_start bs)));
         temp _literal (Vlong (Int64.repr (last_delim bs)));
         temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 9: past the loop: invalid = v, 0 or 1 with a flagged octet. *)
Definition pre9 (gv: globals) (vc: val) (bs: list Z) (pi: val) (init: list Z) (po: val) (v: Z)
  : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_signed; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init; flag_ok bs v)
  LOCAL (temp _invalid (Vint (Int.repr v));
         temp _out po; temp _cap (Vint (Int.repr (Zlength init))); temp _input pi;
         temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count tuint vc)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece9_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi init po v,
  semax Delta_main (pre9 gv vc bs pi init po v) (Ssequence T9 ret0) main_post.
Definition piece8_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi init po,
  semax Delta_main (pre8 gv vc bs pi init po) (Ssequence T8 ret0) main_post.
Definition piece5_stmt : Prop := forall (Espec: OracleKind) gv vc bs pi init po,
  semax Delta_main (pre5 gv vc bs pi init po) (Ssequence T5 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc,
  semax Delta_main (pre0 gv vc) (Ssequence T0 ret0) main_post.
