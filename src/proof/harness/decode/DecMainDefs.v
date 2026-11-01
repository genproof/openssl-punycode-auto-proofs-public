(* The main of harness/x_decode.c in pieces: the cut points of its body, the context, the postcondition and the
   precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`, where T_k
   is the body's top-level sequence from its k-th statement on (what VST shows at that point, followed by
   MORE_COMMANDS = ret0); it takes the piece it continues with as a hypothesis (no piece Requires another one),
   DecMain.v chains them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_decode.code.
Require Import OpensslPunycode.proof.harness.decode.DecProg.

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Fixpoint spine_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ r => spine_drop k' r | _ => s end end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

(* The top-level statements of main_big: 0 len = nondet_size(), 1 enc = malloc, 2 snap = malloc, 3 the NULL test,
   4 if (len != 0) nondet_bytes, 5 copy_bytes, 6 pick(cap), 7 bytes = cap * 4, 8 out = malloc, 9 want = malloc,
   10 the NULL test, 11 the loop, 12 olen = cap, 13 r = ossl_punycode_decode, 14 if (len >= UINT_MAX) .. else
   pr_decode .., 15 gp_assert(same_uints), 16 gp_assert(same_bytes), 17 return 0. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T4 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 4 main_big.
Definition T7 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 7 main_big.
Definition T11 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 11 main_big.
Definition T12 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 12 main_big.
Definition T14 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 14 main_big.
Definition T15 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 15 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

Definition t_dec := Tstruct _pr_dec noattr.

(* What ossl_punycode_decode returns, leaves in out and in olen (PunySpec.decode_result), for the input bs and the
   initial array init of cap = |init| code points. *)
Definition dres (bs init: list Z) : Z * list val * Z :=
  OpensslPunycode.proof.punycode.PunySpec.decode_result bs (Zlength init) (vb init).

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) (vc vo vd: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (data_at_ Tsh tuint vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 4: len = n, enc and snap allocated (past the NULL test: arrays of n octets, none when n = 0, where the
   pointers may be NULL). *)
Definition pre4 (gv: globals) (vc vo vd: val) (n: Z) (pe ps: val) : environ -> mpred :=
  PROP (0 <= n <= Int64.max_unsigned)
  LOCAL (temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr n));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuchar n (Zrepeat Vundef n) pe; arr0 Ews tuchar n (Zrepeat Vundef n) ps;
       data_at_ Tsh tuint vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 7: the input bs drawn (enc) and copied (snap), cap = c drawn. *)
Definition pre7 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (c: Z) : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned)
  LOCAL (temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr c)) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 11: out and want allocated (past the NULL test: arrays of c unsigned ints, none when c = 0). *)
Definition pre11 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (c: Z) (po pw: val)
    : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= c <= Int.max_unsigned)
  LOCAL (temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuint c (Zrepeat Vundef c) po; arr0 Ews tuint c (Zrepeat Vundef c) pw;
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr c)) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 12: after the loop: out and want both hold the drawn initial values init (cap = |init|). *)
Definition pre12 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (init: list Z) (po pw: val)
    : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuint (Zlength init) (vb init) po; arr0 Ews tuint (Zlength init) (vb init) pw;
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr (Zlength init))) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 14: after r = ossl_punycode_decode(enc, len, out, &olen): r, out and olen as decode_result says. *)
Definition pre14 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (init: list Z) (po pw: val)
    : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _r (Vint (Int.repr (fst (fst (dres bs init)))));
         temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuint (Zlength init) (snd (fst (dres bs init))) po; arr0 Ews tuint (Zlength init) (vb init) pw;
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr (Zlength init))) vc;
       data_at Tsh tuint (Vint (Int.repr (snd (dres bs init)))) vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Cut 15: after the checks of r and olen: want holds what out holds (pr_decode's array, or init untouched when
   len >= UINT_MAX). *)
Definition pre15 (gv: globals) (vc vo vd: val) (bs: list Z) (pe ps: val) (init: list Z) (po pw: val)
    : environ -> mpred :=
  PROP (bytes_ok bs; Zlength bs <= Int64.max_unsigned; Zlength init <= Int.max_unsigned;
        Forall (fun x => 0 <= x <= Int.max_unsigned) init)
  LOCAL (temp _want pw; temp _out po; temp _snap ps; temp _enc pe; temp _len (Vlong (Int64.repr (Zlength bs)));
         gvars gv; lvar _cap tuint vc; lvar _olen tuint vo; lvar _d t_dec vd)
  SEP (arr0 Ews tuint (Zlength init) (snd (fst (dres bs init))) po;
       arr0 Ews tuint (Zlength init) (snd (fst (dres bs init))) pw;
       arr0 Ews tuchar (Zlength bs) (vb bs) pe; arr0 Ews tuchar (Zlength bs) (vb bs) ps;
       data_at Tsh tuint (Vint (Int.repr (Zlength init))) vc; data_at_ Tsh tuint vo; data_at_ Tsh t_dec vd;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece15_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd bs pe ps init po pw,
  semax Delta_main (pre15 gv vc vo vd bs pe ps init po pw) (Ssequence T15 ret0) main_post.
Definition piece14_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd bs pe ps init po pw,
  semax Delta_main (pre14 gv vc vo vd bs pe ps init po pw) (Ssequence T14 ret0) main_post.
Definition piece12_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd bs pe ps init po pw,
  semax Delta_main (pre12 gv vc vo vd bs pe ps init po pw) (Ssequence T12 ret0) main_post.
Definition piece11_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd bs pe ps c po pw,
  semax Delta_main (pre11 gv vc vo vd bs pe ps c po pw) (Ssequence T11 ret0) main_post.
Definition piece7_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd bs pe ps c,
  semax Delta_main (pre7 gv vc vo vd bs pe ps c) (Ssequence T7 ret0) main_post.
Definition piece4_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd n pe ps,
  semax Delta_main (pre4 gv vc vo vd n pe ps) (Ssequence T4 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc vo vd,
  semax Delta_main (pre0 gv vc vo vd) (Ssequence T0 ret0) main_post.
