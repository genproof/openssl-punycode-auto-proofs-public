(* The main of harness/rfc_digit_case.c in pieces: the cut points of its body, the context, the postcondition and
   the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where
   T_k is the body's top-level sequence from its k-th statement on; it takes the piece it continues with as a
   hypothesis, RdcMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.rfc_digit_case.code.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcProg.
Require Import OpensslPunycode.proof.laws.rfc_digit_case.RdcModel.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T9 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 9 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

Definition u32s (l: list Z) : Prop := Forall (fun x => 0 <= x <= Int.max_unsigned) l.

(* Cut 0: the start of the body (the constants of punycode.c as its specification wants them, mem_mgr). *)
Definition pre0 (gv: globals) (v1 v2: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count1 tuint v1; lvar _count2 tuint v2)
  SEP (data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

(* Cut 7: past the NULL test: the input bs and the object other (two blocks of |bs| octets, none when bs = []),
   both holding bs, the capacity cap = |init1| = |init2| and the arrays out1, out2 holding init1, init2. *)
Definition pre7 (gv: globals) (v1 v2: val) (bs: list Z) (pi ps: val) (init1: list Z) (po1: val)
    (init2: list Z) (po2: val) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init1 <= Int.max_unsigned;
        Zlength init2 = Zlength init1; u32s init1; u32s init2)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps;
         temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1;
         lvar _count2 tuint v2)
  SEP (arr0 Ews tuint (Zlength init1) (vb init1) po1; arr0 Ews tuint (Zlength init1) (vb init2) po2;
       arr0 Ews tuchar (Zlength bs) (vb bs) ps; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

(* Cut 9: past the loop: other holds bs', which is bs with letters of its deltas in either case. *)
Definition pre9 (gv: globals) (v1 v2: val) (bs bs': list Z) (pi ps: val) (init1: list Z) (po1: val)
    (init2: list Z) (po2: val) : environ -> mpred :=
  PROP (bytes_ok bs; bytes_ok bs'; case_rel (delta_start bs) bs bs'; Zlength bs <= Int64.max_unsigned;
        Zlength init1 <= Int.max_unsigned; Zlength init2 = Zlength init1; u32s init1; u32s init2)
  LOCAL (temp _out2 po2; temp _out1 po1; temp _cap (Vint (Int.repr (Zlength init1))); temp _other ps;
         temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv; lvar _count1 tuint v1;
         lvar _count2 tuint v2)
  SEP (arr0 Ews tuint (Zlength init1) (vb init1) po1; arr0 Ews tuint (Zlength init1) (vb init2) po2;
       arr0 Ews tuchar (Zlength bs) (vb bs') ps; arr0 Ews tuchar (Zlength bs) (vb bs) pi;
       data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece9_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs bs' pi ps init1 po1 init2 po2,
  semax Delta_main (pre9 gv v1 v2 bs bs' pi ps init1 po1 init2 po2) (Ssequence T9 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv v1 v2 bs pi ps init1 po1 init2 po2,
  semax Delta_main (pre7 gv v1 v2 bs pi ps init1 po1 init2 po2) (Ssequence T7 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv v1 v2,
  semax Delta_main (pre0 gv v1 v2) (Ssequence T0 ret0) main_post.
