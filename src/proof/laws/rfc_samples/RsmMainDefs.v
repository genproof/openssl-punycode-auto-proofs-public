(* The main of harness/rfc_samples.c in pieces: the data the harness's globals hold (RsmModel), the cut points of
   main's body, the context, the postcondition and the precondition at each cut. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The globals of the harness                                              *)
(* ---------------------------------------------------------------------- *)

(* The indices of the samples. *)
Definition idx19 : list Z := map Z.of_nat (seq 0 19).

(* The string literal of sample s: its octets and the terminating NUL, as char. *)
Definition lit (gv: globals) (s: Z) : mpred :=
  data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) (gv (Znth s lit_ids)).

(* The separating conjunction of f over a list of indices. *)
Fixpoint sep_list (f: Z -> mpred) (l: list Z) : mpred :=
  match l with [] => emp | a :: r => f a * sep_list f r end.

(* All the literals, and all but the one of sample s. *)
Definition lits (gv: globals) : mpred := sep_list (lit gv) idx19.
Definition lits_but (gv: globals) (s: Z) : mpred :=
  sep_list (lit gv) (sublist 0 s idx19 ++ sublist (s + 1) 19 idx19).

(* encoded[], points[] and decoded[]. *)
Definition encoded_at (gv: globals) : mpred :=
  data_at Ers (tarray (tptr tschar) 19) (map gv lit_ids) (gv _encoded).
Definition points_at (gv: globals) : mpred := data_at Ers (tarray tuchar 19) (vb pts) (gv _points).
Definition decoded_at (gv: globals) : mpred := data_at Ers (tarray tuint 355) (vb dec) (gv _decoded).

(* ---------------------------------------------------------------------- *)
(* The cut points                                                          *)
(* ---------------------------------------------------------------------- *)

Definition main_big : statement := match fn_body f_main with Ssequence b _ => b | s => s end.
Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).
Definition T0 := Eval cbv beta iota delta [main_big f_main fn_body] in main_big.

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The body of the loop over the samples, and its part past the NULL test of out: from count = points[s] to
   free(out). *)
Definition loop_body : statement :=
  Eval cbv beta iota delta [T0] in
  match T0 with Ssequence _ (Ssequence (Ssequence _ (Sloop (Ssequence _ b) _)) _) => b | s => s end.
Definition iterB : statement :=
  Eval cbv beta iota delta [loop_body] in
  match loop_body with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ r))) => r | s => s end.

(* Cut 0: the start of the body. *)
Definition pre0 (gv: globals) (vc: val) : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; lvar _count tuint vc)
  SEP (lits gv; encoded_at gv; points_at gv; decoded_at gv; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* The invariant of the loop over the samples, before sample s: the code points of the first s samples are
   behind. *)
Definition inv (gv: globals) (vc: val) (s: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
  SEP (lits gv; encoded_at gv; points_at gv; decoded_at gv; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

(* Before and after the body of the loop for sample s (the postcondition of forward_for_simple_bound). *)
Definition iter_pre (gv: globals) (vc: val) (s: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _s (Vint (Int.repr s)); temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
  SEP (lits gv; encoded_at gv; points_at gv; decoded_at gv; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).
Definition iter_next (gv: globals) (vc: val) (s: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _s (Vint (Int.repr s)); temp _at (Vlong (Int64.repr (start (s + 1)))); gvars gv;
         lvar _count tuint vc)
  SEP (lits gv; encoded_at gv; points_at gv; decoded_at gv; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).
Definition iter_post (gv: globals) (vc: val) (s: Z) : ret_assert := for_ret_assert (iter_next gv vc s) main_post.

(* Past the NULL test of sample s: the literal at pl (taken out of the others), its length in len, the array out
   of points[s] elements (any values vs) from any_uints. *)
Definition preB (gv: globals) (vc: val) (s: Z) (pl po: val) (vs: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out po; temp _len (Vlong (Int64.repr (Zlength (enc s)))); temp _s (Vint (Int.repr s));
         temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
  SEP (@malloc_token OpensslPunycode.proof.laws.common.HelperSpec.CS Ews (tarray tuint (Znth s pts)) po;
       @arr0 OpensslPunycode.proof.laws.common.HelperSpec.CS Ews tuint (Znth s pts) (vb vs) po;
       data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl;
       lits_but gv s; data_at Ers (tarray (tptr tschar) 19) (map gv lit_ids) (gv _encoded);
       data_at Ers (tarray tuchar 19) (vb pts) (gv _points); decoded_at gv; data_at_ Tsh tuint vc;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT).

Definition pieceB_stmt : Prop := forall (Espec: OracleKind) gv vc s pl po vs,
  0 <= s < 19 -> po <> nullval -> Zlength vs = Znth s pts -> Forall (fun x => 0 <= x <= Int.max_unsigned) vs ->
  Znth s (map gv lit_ids) = pl ->
  lit gv s = data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl ->
  semax Delta_main (preB gv vc s pl po vs) iterB (normal_ret_assert (iter_next gv vc s)).
Definition iter_stmt : Prop := forall (Espec: OracleKind) gv vc s,
  0 <= s < 19 -> semax Delta_main (iter_pre gv vc s) loop_body (iter_post gv vc s).
Definition piece0_stmt : Prop := forall (Espec: OracleKind) gv vc,
  semax Delta_main (pre0 gv vc) (Ssequence T0 ret0) main_post.
