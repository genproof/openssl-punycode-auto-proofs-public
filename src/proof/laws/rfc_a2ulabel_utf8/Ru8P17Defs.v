(* The assertions of the utf8 loop of the main of harness/rfc_a2ulabel_utf8.c (Ru8P17Loop, Ru8P17Put): the octets
   written so far, what the loop knows of valid, size and want, the state at the loop's increment, and the branch of
   the body that writes the octets of one code point. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8P17Lib.
Local Open Scope logic.

(* A loaded element shows as Znth at the reptype's Inhabitant instance: back to the val one. *)
Ltac fixZ := match goal with |- context [@Znth ?A ?d ?i ?l] => change (@Znth A d i l) with (Znth i l) end.

(* The octets of the first j code points of out. *)
Definition ru8p17_w (out: list Z) (j: Z) : list Z := concat (map utf8 (sublist 0 j out)).

(* What the loop knows of valid (v), size (sz) and want (wv) once it has gone through j code points: while valid,
   every one is at most 0x10FFFF and want holds their octets; once not, there is no decoding. *)
Definition ru8p17_ok (s out: list Z) (v0 v: bool) (j sz: Z) (wv: list val) : Prop :=
  if v then v0 = true /\ Forall (fun c => c <= 1114111) (sublist 0 j out) /\ sz = Zlength (ru8p17_w out j) /\
            wv = vb (ru8p17_w out j) ++ Zrepeat Vundef (2049 - sz)
  else ru8_want s = None.

(* The state at the loop's increment j++: code point j done. *)
Definition ru8p17_inc gv vc len s pl pc outlen ob pout psaved pw (v0: bool) (cpsv: list val) (cnt: Z) (out: list Z)
    : environ -> mpred :=
  EX j: Z, EX v: bool, EX sz: Z, EX wv: list val,
  PROP (0 <= j < cnt; 0 <= sz <= 4 * (j + 1); Zlength wv = 2049; ru8p17_ok s out v0 v (j + 1) sz wv)
  LOCAL (temp _j (Vint (Int.repr j)); temp _size (Vlong (Int64.repr sz));
         temp _valid (Vint (Int.repr (if v then 1 else 0)));
         temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
  SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) cpsv pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) wv pw;
       data_at Tsh tuint (Vint (Int.repr cnt)) vc; mem_mgr gv;
       OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT).

(* The branch of the loop body for a code point at most 0x10FFFF: size = size + utf8(cps[j], want + size). *)
Definition ru8p17_put : statement :=
  ltac:(let x := eval cbv [T17] in T17 in
        lazymatch x with
        | Ssequence (Ssequence _ (Sloop (Ssequence _ (Ssequence _ (Sifthenelse _ _ ?b))) _)) _ => exact b
        end).
