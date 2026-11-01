(* The states of the digit loop of encode's branch c == n (TrtEncDig.v): the loop's invariant, the state before its
   increment k = k + 36, the state after it, and the Clight sub-statements of the loop body and of what follows the
   loop (taken from tstmt_digs of TrtEncDefs.v).  The digits written so far are wr: out ++ wr is the output, its
   length is in *len. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Local Open Scope logic.

(* The body of the digit loop (after its leading Sskip) and the statement after the loop. *)
Definition tstmt_digbody : statement :=
  ltac:(let s := eval hnf in tstmt_digs in
        match s with Ssequence _ (Ssequence (Ssequence _ (Sloop (Ssequence Sskip ?b) _)) _) => exact b end).

Definition tstmt_digpost : statement :=
  ltac:(let s := eval hnf in tstmt_digs in
        match s with Ssequence _ (Ssequence (Ssequence _ (Sloop _ _)) ?p) => exact p end).

(* The body after the break test q < t: the digit of q, put, the failure return, q = (q - t) / (36 - t). *)
Definition tstmt_digput : statement :=
  ltac:(let s := eval hnf in tstmt_digbody in
        match s with Ssequence _ (Ssequence _ ?p) => exact p end).

(* What follows the last digit's put and its failure test: adapt, delta = 0, h++. *)
Definition tstmt_digadapt : statement :=
  ltac:(let s := eval hnf in tstmt_digpost in
        match s with Ssequence _ ?p => exact p end).

Section DigAsserts.
Variables (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (n delta bias h b j: Z) (out: list Z).

(* The invariant of the digit loop: wr written, q and k = 36 (65 - f2) for the remaining fuel f2. *)
Definition tdig_inv : environ -> mpred :=
  EX q: Z, EX f2: nat, EX wr: list Z,
    PROP (enc_digits 64 delta 36 bias = wr ++ enc_digits f2 q (36 + 36 * (64 - Z.of_nat f2)) bias;
          0 <= q < 10 ^ Z.of_nat f2; q <= maxint; (f2 <= 64)%nat; Zlength (out ++ wr) <= room)
    LOCAL (temp _q (Vlong (Int64.repr q)); temp _k (Vlong (Int64.repr (36 + 36 * (64 - Z.of_nat f2))));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv (out ++ wr) room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength (out ++ wr)))) pl).

(* Before the increment k = k + 36: the invariant for fuel f2, with k still 36 less. *)
Definition tdig_inc : environ -> mpred :=
  EX q: Z, EX f2: nat, EX wr: list Z,
    PROP (enc_digits 64 delta 36 bias = wr ++ enc_digits f2 q (36 + 36 * (64 - Z.of_nat f2)) bias;
          0 <= q < 10 ^ Z.of_nat f2; q <= maxint; (f2 < 64)%nat; Zlength (out ++ wr) <= room)
    LOCAL (temp _q (Vlong (Int64.repr q)); temp _k (Vlong (Int64.repr (36 * (64 - Z.of_nat f2))));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv (out ++ wr) room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength (out ++ wr)))) pl).

(* After the digit loop: the last digit q remains. *)
Definition tdig_brk : environ -> mpred :=
  EX q: Z, EX wr: list Z,
    PROP (enc_digits 64 delta 36 bias = wr ++ [digit_char q]; 0 <= q < 26; Zlength (out ++ wr) <= room)
    LOCAL (temp _q (Vlong (Int64.repr q));
      temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv (out ++ wr) room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength (out ++ wr)))) pl).

End DigAsserts.
