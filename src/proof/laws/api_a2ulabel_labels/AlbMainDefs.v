(* The main of harness/api_a2ulabel_labels.c in pieces: the cut points of its body, the context, the postcondition
   and the precondition at each cut.  A piece k is `semax Delta_main (pre_k ...) (Ssequence T_k ret0) main_post`,
   where T_k is the body's top-level sequence from its k-th statement on (what VST shows at that point, followed by
   MORE_COMMANDS = ret0); it takes the piece it continues with as a hypothesis, AlbMain.v chains them.  The checks
   need two facts about the model (AlbModel.v); the pieces of the checks take them as hypotheses too. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.harness.api_a2ulabel_labels.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_labels.AlbModel.
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

(* The top-level statements of main_big: 0 len1 = upto(..), 1 len2 = upto(..), 2 s1 = any_bytes(len1 + 1),
   3 s2 = any_bytes(len2 + 1), 4 name = malloc(len1 + len2 + 2), 5 outlen1 = upto(..), 6 outlen2 = upto(..),
   7 out1, 8 out2, 9 out = any_bytes(..), 10 the NULL test, 11 the test of outlen1, outlen2 against 0,
   12 s1[len1] = 0, 13 s2[len2] = 0, 14 n1 = 0, 15 n2 = 0, 16 the copy of s1, 17 name[n1] = '.', 18 the copy of s2,
   19 name[n1 + 1 + n2] = 0, 20 ossl_shim_zalloc_failed = 0, 21 r1 = ossl_a2ulabel(s1, ..), 22 r2 = .. (s2, ..),
   23 r = .. (name, ..), 24 the test of ossl_shim_zalloc_failed, 25 the check of -1, 26 the check of 1 and the
   return. *)
Definition T0 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 0 main_big.
Definition T12 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 12 main_big.
Definition T18 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 18 main_big.
Definition T21 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 21 main_big.
Definition T25 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 25 main_big.
Definition T26 := Eval cbv beta iota delta [spine_drop main_big f_main fn_body] in spine_drop 26 main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The token type of a zero-size out buffer (ossl_a2ulabel_spec's tk; out1, out2, out are never of size 0 at the
   calls). *)
Definition tk0 : type := tarray tuchar 0.

(* ---------------------------------------------------------------------- *)
(* The state at each cut                                                    *)
(* ---------------------------------------------------------------------- *)

(* Cut 0: the start of the body (the globals as the specifications want them, mem_mgr). *)
Definition pre0 (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv)
  SEP (PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 12: past the two tests: s1, s2 hold len1 + 1 and len2 + 1 arbitrary octets, name is uninitialized
   (len1 + len2 + 2 octets), out1, out2, out hold outlen1, outlen2 (both >= 1) and outlen1 + outlen2 arbitrary
   octets.  The malloc tokens are no longer needed (in TT). *)
Definition pre12 (gv: globals) (len1 len2: Z) (bs1 bs2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z)
    (ps1 ps2 pn po1 po2 po: val) : environ -> mpred :=
  PROP (0 <= len1 <= Int64.max_signed - 2; 0 <= len2 <= Int64.max_signed - 2 - len1;
        Zlength bs1 = (len1 + 1)%Z; bytes_ok bs1; Zlength bs2 = (len2 + 1)%Z; bytes_ok bs2;
        1 <= outlen1 <= Int64.max_signed; 1 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob)
  LOCAL (temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
         temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
  SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb bs1) ps1; data_at Ews (tarray tuchar (len2 + 1)) (vb bs2) ps2;
       data_at_ Ews (tarray tuchar (len1 + len2 + 2)) pn;
       data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
       data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 18: past the copy of s1 and the '.': s1 holds a1 then a NUL (a1 its first len1 octets), s2 holds a2 then a
   NUL; name starts with the string of a1 (its octets up to the first NUL) and '.'; n1 is the length of that string,
   n2 is 0. *)
Definition pre18 (gv: globals) (len1 len2: Z) (a1 a2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z)
    (ps1 ps2 pn po1 po2 po: val) : environ -> mpred :=
  PROP (0 <= len1 <= Int64.max_signed - 2; 0 <= len2 <= Int64.max_signed - 2 - len1;
        Zlength a1 = len1; bytes_ok a1; Zlength a2 = len2; bytes_ok a2;
        1 <= outlen1 <= Int64.max_signed; 1 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob)
  LOCAL (temp _n2 (Vlong (Int64.repr 0)); temp _n1 (Vlong (Int64.repr (first0 a1)));
         temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1;
         temp _len2 (Vlong (Int64.repr len2)); temp _len1 (Vlong (Int64.repr len1)); gvars gv)
  SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
       data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
       data_at Ews (tarray tuchar (len1 + len2 + 2))
         (vb (str_of a1 ++ [46]) ++ Zrepeat Vundef (len1 + len2 + 1 - first0 a1)) pn;
       data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
       data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* Cut 21: past the copy of s2, the NUL of name and the reset of the failure flag: name holds the string of a1, '.',
   the string of a2 and a NUL, then uninitialized octets. *)
Definition pre21 (gv: globals) (len1 len2: Z) (a1 a2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z)
    (ps1 ps2 pn po1 po2 po: val) : environ -> mpred :=
  PROP (0 <= len1 <= Int64.max_signed - 2; 0 <= len2 <= Int64.max_signed - 2 - len1;
        Zlength a1 = len1; bytes_ok a1; Zlength a2 = len2; bytes_ok a2;
        1 <= outlen1 <= Int64.max_signed; 1 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob)
  LOCAL (temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); temp _name pn; temp _s2 ps2; temp _s1 ps1; gvars gv)
  SEP (data_at Ews (tarray tuchar (len1 + 1)) (vb (a1 ++ [0])) ps1;
       data_at Ews (tarray tuchar (len2 + 1)) (vb (a2 ++ [0])) ps2;
       data_at Ews (tarray tuchar (len1 + len2 + 2))
         (vb (str_of a1 ++ [46] ++ str_of a2 ++ [0]) ++ Zrepeat Vundef (len1 + len2 - first0 a1 - first0 a2)) pn;
       data_at Ews (tarray tuchar outlen1) (vb ob1) po1; data_at Ews (tarray tuchar outlen2) (vb ob2) po2;
       data_at Ews (tarray tuchar (outlen1 + outlen2)) (vb ob) po;
       PS.puny_consts gv; PS.xn_lit gv; SS.shim_state gv 0 0 0; mem_mgr gv; TT).

(* The octets ossl_a2ulabel leaves in a buffer of cap octets that held init, when no allocation failed. *)
Definition outbuf (s: list Z) (cap: Z) (init: list Z) : list val :=
  vb (snd (a2ulabel s cap)) ++ sublist (Zlength (snd (a2ulabel s cap))) cap (vb init).

(* Cut 25: past the three calls and the test of the failure flag (so no allocation failed): r1, r2, r are the results
   of the model for the strings t1, t2 and t1 '.' t2, and out1, out2, out hold what the model writes. *)
Definition pre25 (gv: globals) (t1 t2: list Z) (outlen1 outlen2: Z) (ob1 ob2 ob: list Z) (po1 po2 po: val)
    : environ -> mpred :=
  PROP (SS.str_ok t1; SS.str_ok t2;
        1 <= outlen1 <= Int64.max_signed; 1 <= outlen2 <= Int64.max_signed - outlen1;
        Zlength ob1 = outlen1; bytes_ok ob1; Zlength ob2 = outlen2; bytes_ok ob2;
        Zlength ob = (outlen1 + outlen2)%Z; bytes_ok ob)
  LOCAL (temp _r (Vint (Int.repr (fst (a2ulabel (t1 ++ [46] ++ t2) (outlen1 + outlen2)))));
         temp _r2 (Vint (Int.repr (fst (a2ulabel t2 outlen2))));
         temp _r1 (Vint (Int.repr (fst (a2ulabel t1 outlen1))));
         temp _out po; temp _out2 po2; temp _out1 po1; temp _outlen2 (Vlong (Int64.repr outlen2));
         temp _outlen1 (Vlong (Int64.repr outlen1)); gvars gv)
  SEP (data_at Ews (tarray tuchar outlen1) (outbuf t1 outlen1 ob1) po1;
       data_at Ews (tarray tuchar outlen2) (outbuf t2 outlen2 ob2) po2;
       data_at Ews (tarray tuchar (outlen1 + outlen2)) (outbuf (t1 ++ [46] ++ t2) (outlen1 + outlen2) ob) po;
       TT).

(* ---------------------------------------------------------------------- *)
(* The model facts the checks need (AlbModel.v)                            *)
(* ---------------------------------------------------------------------- *)

Definition join_minus1_stmt : Prop := forall s1 s2 c1 c2 c,
  0 <= c1 -> 0 <= c2 -> 0 <= c ->
  fst (a2ulabel s1 c1) = -1 \/ fst (a2ulabel s2 c2) = -1 ->
  fst (a2ulabel (s1 ++ [46] ++ s2) c) = -1.

Definition join_one_stmt : Prop := forall s1 s2 c1 c2 w1 w2,
  SS.str_ok s1 -> SS.str_ok s2 -> 0 <= c1 -> 0 <= c2 ->
  a2ulabel s1 c1 = (1, w1) -> a2ulabel s2 c2 = (1, w2) ->
  exists w1' w2', w1 = w1' ++ [0] /\ w2 = w2' ++ [0] /\
    Forall (fun b => 1 <= b <= 255) w1' /\ Forall (fun b => 1 <= b <= 255) w2' /\
    Zlength w1 <= c1 /\ Zlength w2 <= c2 /\
    a2ulabel (s1 ++ [46] ++ s2) (c1 + c2) = (1, w1' ++ [46] ++ w2).

(* ---------------------------------------------------------------------- *)
(* The pieces' statements                                                  *)
(* ---------------------------------------------------------------------- *)

Definition piece26_stmt : Prop := forall (Espec: OracleKind) gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po,
  semax Delta_main (pre25 gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po) (Ssequence T26 ret0) main_post.
Definition piece25_stmt : Prop := forall (Espec: OracleKind) gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po,
  semax Delta_main (pre25 gv t1 t2 outlen1 outlen2 ob1 ob2 ob po1 po2 po) (Ssequence T25 ret0) main_post.
Definition piece21_stmt : Prop := forall (Espec: OracleKind) gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob
    ps1 ps2 pn po1 po2 po,
  semax Delta_main (pre21 gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po)
    (Ssequence T21 ret0) main_post.
Definition piece18_stmt : Prop := forall (Espec: OracleKind) gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob
    ps1 ps2 pn po1 po2 po,
  semax Delta_main (pre18 gv len1 len2 a1 a2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po)
    (Ssequence T18 ret0) main_post.
Definition piece12_stmt : Prop := forall (Espec: OracleKind) gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob
    ps1 ps2 pn po1 po2 po,
  semax Delta_main (pre12 gv len1 len2 bs1 bs2 outlen1 outlen2 ob1 ob2 ob ps1 ps2 pn po1 po2 po)
    (Ssequence T12 ret0) main_post.
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv,
  semax Delta_main (pre0 gv) (Ssequence T0 ret0) main_post.
